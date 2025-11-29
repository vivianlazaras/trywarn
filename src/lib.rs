#![deny(missing_docs)]
#![deny(dead_code)]
#![deny(unused_variables)]

//! # Warnable
//!
//! This crate provides the `Warnable` type, a wrapper around a value that may
//! have associated non-fatal warnings. The warnings can be automatically logged
//! via a `Logger` implementation, propagated manually, or ignored.  
//!
//! Features:
//! - Attach warnings to a value without failing.
//! - Automatic logging in debug builds and in `Drop`.
//! - Optional manual propagation of warnings via `propagate()` or `unwrap()`.
//! - Works with custom logging mechanisms.
//!
//! # Examples
//!
//! ```rust
//! use trywarn::{Warnable, StdErrLogger};
//! use std::fmt;
//!
//! #[derive(Debug)]
//! struct MyWarning(&'static str);
//!
//! impl fmt::Display for MyWarning {
//!     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//!         write!(f, "{}", self.0)
//!     }
//! }
//!
//! impl std::error::Error for MyWarning {}
//!
//! let wrapped = Warnable::new(42, Some(MyWarning("minor issue")), StdErrLogger);
//! let value = wrapped.unwrap(); // logs warning and returns 42
//! assert_eq!(value, 42);
//! ```

#![cfg_attr(feature = "try", feature(try_trait_v2))]
#[cfg(feature = "try")]
mod tryable;

pub use paste::paste;

mod macros;

use std::fmt;
use std::panic;
use std::mem::ManuallyDrop;
use std::panic::{AssertUnwindSafe};
use std::panic::Location;
use std::sync::Arc;

use std::ops::Deref;

/// The default warning type used by `Warnable` macros (`warninit!`, `try_warn!`, `ret!`) 
/// when no explicit warning type is specified.
///
/// `DefaultWarning` is a simple, ergonomic wrapper around a `String` that implements
/// `std::error::Error`, `Display`, and other common traits for easy integration.
///
/// # Example
///
/// ```rust
/// use your_crate::DefaultWarning;
///
/// let w1 = DefaultWarning::new("something minor happened");
/// let w2: DefaultWarning = "static warning".into();
///
/// println!("{}", w1); // prints: something minor happened
/// ```
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct DefaultWarning {
    message: String,
}

impl DefaultWarning {
    /// Creates a new `DefaultWarning` from any type that can convert into a `String`.
    ///
    /// # Arguments
    ///
    /// * `msg` — The message content
    ///
    /// # Example
    ///
    /// ```rust
    /// use your_crate::DefaultWarning;
    /// let w = DefaultWarning::new("minor warning");
    /// ```
    pub fn new<S: Into<String>>(msg: S) -> Self {
        Self { message: msg.into() }
    }
}

impl fmt::Display for DefaultWarning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for DefaultWarning {}

impl From<&'static str> for DefaultWarning {
    fn from(s: &'static str) -> Self {
        Self::new(s)
    }
}

impl From<String> for DefaultWarning {
    fn from(s: String) -> Self {
        Self::new(s)
    }
}

impl AsRef<str> for DefaultWarning {
    fn as_ref(&self) -> &str {
        &self.message
    }
}

impl Deref for DefaultWarning {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        &self.message
    }
}

// Optional: allow `&DefaultWarning` to be printed as &str
impl std::borrow::Borrow<str> for DefaultWarning {
    fn borrow(&self) -> &str {
        &self.message
    }
}

/// The default logger used by `Warnable` when no custom logger is specified.
///
/// `StdErrLogger` prints warnings to standard error with yellow coloring.  
/// This type alias provides a convenient default for users who do not need
/// a custom logging implementation.
pub type DefaultLogger = StdErrLogger;

/// A convenience `Result` type specialized for `Warnable`.
///
/// This type alias wraps a `Warnable<T, E, L>` in a `std::result::Result`, providing
/// a familiar `Result`-style API for functions that may produce warnings.
///
/// # Type Parameters
///
/// - `T`: The main value type wrapped in `Warnable`.
/// - `E`: The error type for the `Result`.
/// - `L`: The logger type used by the `Warnable`. Defaults to [`DefaultLogger`].
///
/// # Example
///
/// ```rust
/// use trywarn::{Warnable, Result, DefaultLogger, StdErrLogger};
///
/// fn compute() -> Result<i32, &'static str> {
///     let value = 42;
///     Ok(Warnable::new(value, None, StdErrLogger))
/// }
/// ```
pub type Result<T, E, L = DefaultLogger> = std::result::Result<Warnable<T, E, L>, E>;

/// Logger trait for warnings.
/// 
/// Users can implement custom logging, storage, or promotion.  
/// 
/// # Type Parameters
///
/// - `W`: The warning type, must implement `std::error::Error`.
///
/// # Notes
///
/// - The `log` method is called with the location of the **last caller outside `Warnable`/`WithWarnings`** via `#[track_caller]`.
/// - Implementations should generally be panic-safe, especially if logging occurs in `Drop`.
pub trait Logger<W: std::error::Error>: Send + Sync {
    
    /// Logs a warning with its call site.
    ///
    /// # Parameters
    ///
    /// - `warning`: The warning instance to log.
    /// - `location`: The call site where the warning originated.
    ///
    /// # Behavior
    ///
    /// The default behavior depends on the implementation, but typically
    /// this method prints or stores the warning along with its location.
    #[track_caller]
    fn log(&self, warning: &W, location: &std::panic::Location);
    
    /// a means of diffrentiating a warning from a log entry.
    #[track_caller]
    fn warn(&self, warning: &W, location: &Location) {
        self.log(warning, location)
    }
}

/// Represents a warning that has been tracked along with its creation context.
///
/// `TrackedWarning` is used internally by `Warnable` to capture not only the warning
/// itself, but also metadata about **where** it was generated and whether it should
/// be logged only in debug builds.
///
/// # Type Parameters
///
/// - `W`: The warning type. Must implement `std::error::Error`.
///
/// # Fields
///
/// - `site`: The call site where this warning was created, e.g., the location of a
///   `warn!` macro invocation. Useful for logging and debugging to pinpoint the origin
///   of the warning.
///
/// - `warning`: The actual warning value of type `W`. Can be any error type that
///   implements `std::error::Error`.
///
/// - `debug_only`: Determines whether this warning should only be logged in debug
///   builds. If `true`, the warning is suppressed in release builds (`cfg!(debug_assertions)`
///   is `false`), allowing non-critical warnings to avoid cluttering production logs.
///
/// # Examples
///
/// ```rust
/// use std::panic::Location;
/// use trywarn::TrackedWarning;
///
/// #[derive(Debug)]
/// struct MyWarning(&'static str);
/// impl std::fmt::Display for MyWarning {
///     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
///         write!(f, "{}", self.0)
///     }
/// }
/// impl std::error::Error for MyWarning {}
///
/// let warning = MyWarning("minor deviation");
/// let tracked = TrackedWarning {
///     site: Location::caller(),
///     warning,
///     debug_only: true,
/// };
///
/// println!("{:?}", tracked);
/// ```
#[derive(Debug)]
pub struct TrackedWarning<W: std::error::Error> {
    /// the call site at which this warning was created (such as where `warn!` was used)
    pub site: &'static Location<'static>,
    /// the underlying warning for this type.
    pub warning: W,
    /// per warning debug preference, if set to true this warning will only be logged if `cfg!(debug_assertions)` is turned on.
    /// as such it won't be logged on release builds.
    pub debug_only: bool,
}

impl<W: std::error::Error> fmt::Display for TrackedWarning<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{}:{}", self.site.file(), self.site.line(), self.site.column(), self.warning)
    }
}

/// Creates a new [`TrackedWarning`] instance.
///
/// Captures the call site where this warning was created using `#[track_caller]`,
/// so logging can reference the file, line, and column where the warning originated.
///
/// # Parameters
///
/// - `warning`: The underlying warning value of type `W`.
/// - `debug_only`: If `true`, this warning will only be logged in debug builds
///   (`cfg!(debug_assertions)`), and will be ignored in release builds.
///
/// # Returns
///
/// A new `TrackedWarning<W>` instance that can be stored in a `Warnable` or
/// passed along to logging facilities.
///
/// # Example
///
/// ```rust
/// use trywarn::{TrackedWarning, DefaultWarning};
///
/// let w = TrackedWarning::new(DefaultWarning::from("something minor happened"), true);
/// ```
impl<W: std::error::Error> TrackedWarning<W> {
    /// construct a new warning using `std::panic::Location::caller()` to determine callsite.
    /// with a parameter to determine if the warning should be outputted on release builds, or only on debug builds.
    #[track_caller]
    pub fn new(warning: W, debug_only: bool) -> Self {
        Self {
            site: Location::caller(),
            warning,
            debug_only,
        }
    }
}

/// A value paired with one or more warnings that occurred during its production or processing.
///
/// `Warnable` is useful when a value is valid and usable, but **non-fatal warnings** occurred  
/// that the caller may wish to inspect, log, or otherwise handle.
///
/// # Type Parameters
///
/// - `T`: The main value type. Can be any type, no trait bounds required.
/// - `W`: The warning type. Must implement `std::error::Error`.
/// - `L`: The logger type. Must implement `Logger<W>`. Defaults to `StdErrLogger`.
///
/// # Behavior
///
/// - Warnings are **logged automatically** if `?` is used (via `Try::branch`) or when `propagate()` is called.
/// - Optional `debug_only` flag allows warnings to only appear in debug builds.
/// - Warnings are also logged in `Drop` as a **safety net** if they were never propagated.
///
/// # Example
///
/// ```rust
/// use trywarn::{Warnable, StdErrLogger};
/// use std::fmt;
///
/// #[derive(Debug)]
/// struct MyWarning(&'static str);
///
/// impl fmt::Display for MyWarning {
///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
///         write!(f, "{}", self.0)
///     }
/// }
///
/// impl std::error::Error for MyWarning {}
///
/// let value = 42;
/// let warning = MyWarning("minor deviation occurred");
///
/// let wrapped = Warnable::new(value, Some(warning), StdErrLogger);
///
/// println!("{:?}", wrapped); // prints Warnable { value: 42, warnings: [...] }
/// ```
pub struct Warnable<T, W: std::error::Error, L: Logger<W> + 'static = DefaultLogger> {
    /// The main value
    value: ManuallyDrop<T>,
    /// Any warnings associated with this value
    warnings: ManuallyDrop<Vec<TrackedWarning<W>>>,
    messages: ManuallyDrop<Vec<TrackedWarning<W>>>,
    /// Logger used to report warnings
    pub logger: Arc<L>,
    /// Optional debug-only flag; if true, warnings are only logged in debug builds
    pub debug_only: bool,
    /// Tracks whether warnings have already been logged
    has_warned: bool,
    filters: WarningFilters<W>,
}

/*
pub enum FilterOutcome<'a, W: std::error::Error> {
    /// Warning matched a deny rule and should cause escalation (panic/error)
    Deny(&'a TrackedWarning<W>),

    /// Warning matched an allow rule and should be removed/suppressed
    Allow(&'a TrackedWarning<W>),

    /// Warning did not match allow or deny — keep and propagate
    Keep(&'a TrackedWarning<W>),
}*/

/// This structure is a streamlined way to return the result of applying `WarningFilters::apply` over a slice of `TrackWarning`
pub struct FilterResult<'a, W: std::error::Error> {
    /// a vector of warnings to retain after deny, and allow filters have been processed.
    pub kept: Vec<&'a TrackedWarning<W>>,
    /// the list of filters removed (allowed) while processing `WarningFilters::apply`
    pub allowed: Vec<&'a TrackedWarning<W>>,
    /// the list of denied warnings that will cause a panic / conversion to `Result::Err` produced from `WarningFilters::apply`
    pub denied: Vec<&'a TrackedWarning<W>>,
}

/// A set of filters to selectively allow or deny warnings of type `W`.
///
/// `WarningFilters` can hold multiple `allow` and `deny` conditions
/// for a given warning type. Each condition is a closure that evaluates
/// the warning and returns `true` if it matches the filter.
///
/// # Type Parameters
///
/// - `W`: The warning type, which must implement `std::error::Error`.
///
/// # Semantics
///
/// - **Deny filters** have the highest precedence: if any deny filter
///   returns `true`, the warning is immediately classified as denied.
/// - **Allow filters** are applied after deny filters: if any allow filter
///   returns `true` (and the warning was not denied), the warning is classified
///   as allowed.
/// - Warnings that match neither deny nor allow filters are considered
///   kept for further propagation.
///
/// # Notes
///
/// - Multiple conditions are combined using logical OR (`||`) for both
///   `allow` and `deny` lists.
/// - Using `Arc<dyn Fn(&W) -> bool>` allows sharing filters across multiple
///   `WarningFilters` instances safely.
#[allow(clippy::type_complexity)]
pub struct WarningFilters<W> {
    allow: Vec<Arc<dyn Fn(&W) -> bool>>,
    deny: Vec<Arc<dyn Fn(&W) -> bool>>,
}

impl<W> Clone for WarningFilters<W> {
    fn clone(&self) -> WarningFilters<W> {
        Self {
            allow: self.allow.clone(),
            deny: self.deny.clone()
        }
    }
}

impl<W> Default for WarningFilters<W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W> WarningFilters<W> {
    /// Create a new empty filter set
    pub fn new() -> Self {
        Self {
            allow: Vec::new(),
            deny: Vec::new(),
        }
    }

    /// Add an allow filter. Multiple allow filters are combined using **OR**.
    pub fn allow<F>(&mut self, f: F) -> &mut Self
    where
        F: Fn(&W) -> bool + Send + Sync + 'static,
    {
        self.allow.push(Arc::new(f));
        self
    }

    /// Add a deny filter. Multiple deny filters are combined using **OR**.
    /// Deny has the highest precedence: if any deny filter matches, the warning is rejected.
    pub fn deny<F>(&mut self, f: F) -> &mut Self
    where
        F: Fn(&W) -> bool + Send + Sync + 'static,
    {
        self.deny.push(Arc::new(f));
        self
    }

}

impl<W: std::error::Error> WarningFilters<W> {
    /// Apply all filters to a slice of warnings
    pub fn apply<'a>(&self, warnings: &'a [TrackedWarning<W>]) -> FilterResult<'a, W> {
        let mut kept = Vec::new();
        let mut allowed = Vec::new();
        let mut denied = Vec::new();

        for w in warnings {
            // Deny filters first (highest precedence)
            if self.deny.iter().any(|d| d(&w.warning)) {
                denied.push(w);
                continue;
            }

            // Allow filters next
            if !self.allow.is_empty() && self.allow.iter().any(|a| a(&w.warning)) {
                allowed.push(w);
                continue;
            }

            // No matching filter → keep propagating
            kept.push(w);
        }

        FilterResult { kept, allowed, denied }
    }
}

impl<T: fmt::Debug, W: std::error::Error> fmt::Debug for Warnable<T, W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Warnable")
            .field("value", &self.value)
            .field("warnings", &self.warnings) // prints using Debug, W: Error requires Debug
            .finish()
    }
}

impl<T, W: std::error::Error, L: Logger<W> + 'static> Warnable<T, W, L> {
    /// Create a new `Warnable` instance with an optional initial warning.
    ///
    /// # Arguments
    ///
    /// - `value`: The primary value.
    /// - `warning`: An optional initial warning.
    /// - `logger`: The logger to use for reporting warnings.
    #[track_caller]
    pub fn new(value: T, warning: Option<W>, logger: L) -> Self
    where
        L: Logger<W> + 'static,
    {
        let site = std::panic::Location::caller();
        let warnings = ManuallyDrop::new(warning.into_iter().map(|warning| TrackedWarning { site, warning, debug_only: false }).collect());
        let messages = ManuallyDrop::new(Vec::new());
        Self {
            value: ManuallyDrop::new(value),
            messages,
            warnings,
            logger: Arc::new(logger),
            debug_only: false,
            has_warned: false,
            filters: WarningFilters::new(),

        }
    }

    /// updates `debug_only` to the given value.
    pub fn set_debug_only(&mut self, debug_only: bool) {
        self.debug_only = debug_only;
    }

    /// converts this `Warnable` into `std::result::Result` returning  `Result::Err` for any denied warnings. 
    pub fn into_result(self) -> core::result::Result<T, Vec<TrackedWarning<W>>> {
        // this makes sense as behavior because `Result` is a stricter type.
        let value = self.hide();
        // for now this isn't very exciting, but once deny is implemented, it'll be far more meaningful
        Ok(value)
    }

    /// as it implies returns a list of contained warnings as an immutable slice.
    pub fn warnings(&self) -> &[TrackedWarning<W>] {
        &self.warnings
    }

    /// just a simple helper function that checks the length of `self.warnings`
    pub fn is_empty(&self) -> bool {
        self.warnings.len() != 0
    }

    /*pub fn from_warnings(value: T, warnings: Vec<TrackedWarning<W>>, logger: L, debug_only: bool) -> Self {
        Self {
            value: ManuallyDrop::new(value),
            warnings: ManuallyDrop::new(warnings),
            has_warned: false,
            logger: Arc::new(logger),
            debug_only,
            filters: WarningFilters::new(),
        }
    }*/

    /// set a filter style callback for allowed warnings.
    pub fn allow<F: Fn(&W) -> bool + Send + Sync + 'static>(mut self, filter: F) -> Self {
        self.filters.allow(filter);
        self
    }

    /// adds a function to the WarningsFilters to match any denied warning.
    pub fn deny<F: Fn(&W) -> bool + Send + Sync + 'static>(mut self, filter: F) -> Self {
        self.filters.deny(filter);
        self
    }

    /// Log all warnings if they haven’t already been logged.
    ///
    /// Uses `#[track_caller]` to capture the last callsite outside `Warnable`.
    #[track_caller]
    fn warn_internal(&mut self) {
        if !self.has_warned {
            self.has_warned = true;
            if cfg!(debug_assertions) || !self.debug_only {
                for tracked in self.warnings.iter() {
                    self.logger.warn(&tracked.warning, tracked.site);
                }
            }
        }
    }

    /// Unwraps the internal value, logging any queued warnings in the process.
    ///
    /// Warnings will be logged at the callsite due to `#[track_caller]`.
    ///
    /// ## Behavior notes
    ///
    /// - Calling `unwrap` consumes `self`.
    /// - Warnings are logged eagerly here, even though they would also be logged
    ///   upon drop if never propagated.
    /// - After extraction, the `Warnable` is left in a state where its `Drop`
    ///   implementation will not attempt to access the taken value.
    ///
    /// # Safety
    ///
    /// This function calls `unsafe { ManuallyDrop::take(&mut self.value) }`.
    /// This is sound because:
    ///
    /// - `value` is stored inside a `ManuallyDrop<T>`, which guarantees that it
    ///   will not be dropped automatically.
    /// - After `take`, `self.has_warned` has been set and `Drop` will not attempt
    ///   to log warnings again.
    /// - No other code path can read or drop the moved-out value.
    ///
    /// The type’s `Drop` implementation upholds the invariant that the inner
    /// value is never dropped twice nor accessed after move.
    #[track_caller]
    pub fn unwrap(mut self) -> T {
        // redundant
        self.warn_internal();
        unsafe { ManuallyDrop::take(&mut self.value) }
    }

    /// empties `self.warnings` replacing it with an empty `Vec` and logging the warnings.
    #[track_caller]
    pub fn flush(&mut self) {
        let warnings = unsafe { ManuallyDrop::take(&mut self.warnings) };
        for tracked in warnings.into_iter() {
            self.logger.log(&tracked.warning, tracked.site);
        }
        self.warnings = ManuallyDrop::new(Vec::new());
    }

    /// Returns the underlying value while suppressing all warnings.
    ///
    /// This marks the warnings as already handled so they will not be printed
    /// during drop, and then extracts the value.
    ///
    /// ## When to use
    ///
    /// - When warnings are expected and intentionally ignored.
    /// - When using higher-level aggregation of warnings elsewhere.
    ///
    /// # Safety
    ///
    /// This method delegates to [`unwrap`](#method.unwrap), inheriting its
    /// safety guarantees regarding the internal `ManuallyDrop::take`.
    ///
    /// Additionally:
    ///
    /// - `self.has_warned = true` ensures that `Drop` will not attempt to log.
    /// - No warnings are accessed after being marked as handled.
    #[track_caller]
    pub fn hide(mut self) -> T {
        self.has_warned = true;
        self.unwrap()
    }
    
    /// Deconstructs the `Warnable` into its underlying value and collected warnings.
    ///
    /// This function is useful when the caller wants to inspect or aggregate warnings
    /// manually rather than letting the logger handle them.
    ///
    /// ## Behavior notes
    ///
    /// - Consumes the `Warnable`.
    /// - Prevents the `Drop` implementation from logging warnings.
    /// - Returns both the extracted value and the full `Vec` of tracked warnings.
    ///
    /// # Safety
    ///
    /// This method performs:
    ///
    /// ```ignore
    /// unsafe { ManuallyDrop::take(&mut self.value) };
    /// unsafe { ManuallyDrop::take(&mut self.warnings) };
    /// ```
    ///
    /// This is sound because:
    ///
    /// - Both fields are wrapped in `ManuallyDrop`, guaranteeing they are not
    ///   automatically dropped by Rust.
    /// - After taking, the struct is left in a state where:
    ///   - `Drop` will not log warnings (`has_warned = true`)
    ///   - `Drop` will not attempt to access the moved-out warnings vector.
    /// - No other reference to the values exists, preventing double drops or use-after-move.
    ///
    /// The `Warnable` type maintains a strict invariant that values extracted via
    /// `take` are never accessed again, ensuring memory safety.
    #[track_caller]
    pub fn unwrap_into_warnings(mut self) -> (T, Vec<TrackedWarning<W>>) {
        self.has_warned = true;
        let value = unsafe { ManuallyDrop::take(&mut self.value) };
        let warnings = unsafe { ManuallyDrop::take(&mut self.warnings) };
        (value, warnings)
    }

    /// Merge this `Warnable` into another `Warnable`.
    ///
    /// This function **moves all warnings from `self` into `other`** instead of logging them immediately.
    /// The value contained in `self` is returned.
    ///
    /// # Use Case
    ///
    /// Use `merge` when a function produces a `Warnable` value but you want the **caller** to
    /// handle all warnings for a callstack, instead of logging them immediately at the point
    /// of production. This is useful for hierarchical or compositional operations where warnings
    /// should be aggregated.
    ///
    /// # Behavior
    ///
    /// - All warnings from `self` are moved into `other`.
    /// - `self.has_warned` is set to `true` to prevent logging during `Drop`.
    /// - `self.value` is extracted using `ManuallyDrop::take` and returned.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use trywarn::{Warnable, StdErrLogger};
    /// # use std::fmt;
    /// #[derive(Debug)]
    /// struct MyWarning(&'static str);
    /// impl fmt::Display for MyWarning {
    ///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self.0) }
    /// }
    /// impl std::error::Error for MyWarning {}
    ///
    /// let a: Warnable<i32, MyWarning, StdErrLogger> = Warnable::warning(10, MyWarning("minor A"), StdErrLogger);
    /// let mut b = Warnable::warning(20, MyWarning("minor B"), StdErrLogger);
    ///
    /// let value_a = a.merge(&mut b);
    /// assert_eq!(value_a, 10);
    /// assert_eq!(b.warnings().len(), 2); // warnings from both `a` and `b`
    /// ```
    pub fn merge(self, other: &mut Self) -> T {
        let (value, warnings) = self.unwrap_into_warnings();
        for warning in warnings.into_iter() {
            other.warnings.push(warning);
        }
        value
    }

    /// Records a warning to be associated with this value.
    ///
    /// This method allows producers to attach a non-fatal warning to the
    /// wrapped value while continuing normal control flow. Warnings are
    /// accumulated and will be logged when the `Warnable<T, W>` is dropped
    /// or when `unwrap()` (or other extraction methods) are called.
    ///
    /// Each warning is paired with its call site via [`Location::caller`],
    /// enabling downstream consumers to trace where the warning originated.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use trywarn::{Warnable};
    /// use thiserror::Error;
    /// #[derive(Debug, Error)]
    /// pub enum MyWarning {
    ///     #[error("missing metadata")]
    ///     MissingMetadata,
    /// }
    /// let mut value = Warnable::new(42, None, StdErrLogger);
    /// value.warn(MyWarning::MissingMetadata);
    /// // continue processing...
    ///
    /// let result = value.unwrap(); // logs accumulated warnings
    /// ```
    ///
    /// # Behavior
    ///
    /// - Warnings do **not** short-circuit evaluation.
    /// - Multiple warnings may be recorded.
    /// - Logged automatically on drop unless already consumed.
    /// - Extracting with `unwrap_without_warnings` or `unwrap_into_warnings`
    ///   marks warnings as handled and prevents automatic logging.
    ///
    /// # Safety
    ///
    /// This method does **not** perform any unsafe operations.
    /// It only appends to the internal warnings collection.
    #[track_caller]
    pub fn warn(&mut self, warning: impl Into<W>) {
        let site = Location::caller();
        let tracked = TrackedWarning { warning: warning.into(), site, debug_only: self.debug_only };
        self.warnings.push(tracked);
    }

    /// Records a warning to be associated with this value.
    ///
    /// This method allows producers to attach a non-fatal warning to the
    /// wrapped value while continuing normal control flow. Warnings are
    /// accumulated and will be logged when the `Warnable<T, W>` is dropped
    /// or when `unwrap()` (or other extraction methods) are called.
    ///
    /// Each warning is paired with its call site via [`Location::caller`],
    /// enabling downstream consumers to trace where the warning originated.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use trywarn::{Warnable};
    /// use thiserror::Error;
    /// #[derive(Debug, Error)]
    /// pub enum MyWarning {
    ///     #[error("missing metadata")]
    ///     MissingMetadata,
    /// }
    /// let mut value = Warnable::new(42, None, StdErrLogger);
    /// value.warn(MyWarning::MissingMetadata);
    /// // continue processing...
    ///
    /// let result = value.unwrap(); // logs accumulated warnings
    /// ```
    ///
    /// # Behavior
    ///
    /// - Warnings do **not** short-circuit evaluation.
    /// - Multiple warnings may be recorded.
    /// - Logged automatically on drop unless already consumed.
    /// - Extracting with `unwrap_without_warnings` or `unwrap_into_warnings`
    ///   marks warnings as handled and prevents automatic logging.
    ///
    /// # Safety
    ///
    /// This method does **not** perform any unsafe operations.
    /// It only appends to the internal warnings collection.
    #[track_caller]
    pub fn debug(&mut self, warning: impl Into<W>) {
        let site = Location::caller();
        let tracked = TrackedWarning { warning: warning.into(), site, debug_only: true };
        self.warnings.push(tracked);
    }

    /// create an instance of warnable without any warnings.
    #[track_caller]
    pub fn clear(value: T, logger: L) -> Self {
        Self::new(value, None, logger)
    }

    /// create an instance with a single warning set.
    #[track_caller]
    pub fn warning(value: T, warning: W, logger: L) -> Self {
        Self::new(value, Some(warning), logger)
    }
}

/*impl<T, L: Logger<Box<dyn std::error::Error>>> Warnable<T, Box<dyn std::error::Error>, L> {
    /// Add a deny filter that rejects warnings of type `W`
    pub fn deny_by_type<W>(&mut self)
    where
        W: std::error::Error + 'static,
    {
        self.deny(|warning: &Box<dyn std::error::Error>| {
            // Attempt downcast to concrete type
            warning.as_ref().type_id() == TypeId::of::<W>()
        });
    }
}*/

impl<T, W: std::error::Error, L: Logger<W>> Warnable<Option<T>, W, L> {
    /// create's an uninitialized `Warnable` using `None`
    pub fn new_uninitialized(logger: L, debug_only: bool) -> Self {
        let mut instance = Warnable::new(None, None, logger);
        instance.set_debug_only(debug_only);
        instance
    }

    /// set's the underlying value withing the `Option`
    pub fn set_value(mut self, v: T) -> Self {
        self.value = ManuallyDrop::new(Some(v));
        self
    }

    /// Converts a `Warnable<Option<T>>` into a `Warnable<T>`,
    /// extracting the inner value and warnings from their
    /// ManuallyDrop containers without double-drop.
    ///
    /// # Panics
    ///
    /// * Panics if the value is still `None`
    ///
    /// # Safety
    ///
    /// This function performs `ManuallyDrop::take` on both the value
    /// and warning fields. This is safe **only because**:
    ///
    /// * `Warnable` guarantees these fields will not be dropped again
    /// * `self` is consumed, preventing further access
    ///
    #[doc(hidden)]
    pub fn unoptionize(mut self) -> Warnable<T, W, L> {
        // don't warn when this instance is dropped.
        self.has_warned = true;
        // Take the Option<T> out of ManuallyDrop
        let value_opt = unsafe { ManuallyDrop::take(&mut self.value) };

        // Take the warnings vector out of ManuallyDrop
        let warnings_vec = unsafe { ManuallyDrop::take(&mut self.warnings) };
        let messages_vec = unsafe { ManuallyDrop::take(&mut self.messages) };
        // Extract the logger (by move)
        let logger = self.logger.clone();
        let filters = self.filters.clone();

        // Extract debug flag
        let debug_only = self.debug_only;

        // Convert None → panic (alternative semantics possible)
        let value = value_opt.expect("unoptionize() called before a value was set");
    
        
        Warnable {
            value: ManuallyDrop::new(value),
            warnings: ManuallyDrop::new(warnings_vec),
            messages: ManuallyDrop::new(messages_vec),
            logger,
            debug_only,
            has_warned: false,
            filters
        }
    }
}

/// Default logger that prints warnings to `stderr` in yellow.
#[derive(Debug, Clone, Copy, Default)]
pub struct StdErrLogger;

impl<W: std::error::Error> Logger<W> for StdErrLogger {
    /// logs the given warning to stderr using yellow ascii text escapes.
    fn log(&self, warning: &W, location: &std::panic::Location) {
        eprintln!("\x1b[33m[Warning]: {}:{}:{} {}\x1b[0m", location.file(), location.line(), location.column(), warning);
    }
}

/// Ensure warnings are logged even if the `Warnable` is dropped without unwrap.
impl<T, W: std::error::Error, L: Logger<W> + 'static> Drop for Warnable<T, W, L> {
    fn drop(&mut self) {
        // in case the logger could panic, so a double panic doesn't occur (which causes process termination.)
        let _ = panic::catch_unwind(AssertUnwindSafe(|| {
            self.warn_internal();
        }));
    }
}

/// A helper trait for converting `Result` and `Option` types into a
/// `Warnable<(), W, L>` when the caller does **not** care about the returned
/// value, but still wants to record warnings if the value is absent or an
/// error occurred.
///
/// This is useful in situations where:
///
/// - a computation may fail, but failure is *non-fatal*
/// - the value being returned is irrelevant to the caller
/// - warnings should be accumulated and handled later
/// - control flow should **not** short-circuit like `?` normally would
///
/// The name *trivialize* reflects that the value itself is treated as
/// semantically trivial — only the presence of a warning matters.
///
/// # Type Parameters
///
/// - `W`: The warning/error type to store inside the resulting `Warnable`.Must implement `std::error::Error`.
/// - `L`: Logger type used to record warnings, implementing `Logger<W>`.
///
/// # Behavior
///
/// Calling `trivialize`:
///
/// - For `Result<T, E>`:
///   * `Ok(_)` → produces a `Warnable` with no warnings
///   * `Err(e)` → produces a `Warnable` containing a warning derived from `e`
///
/// - For `Option<T>`:
///   * `Some(_)` → produces a `Warnable` with no warnings
///   * `None` → produces a `Warnable` with a warning generated for the absence
///
/// # Why use this?
///
/// This allows you to:
///
/// - ignore `Result` / `Option` values while still keeping diagnostic context
/// - avoid panics, early returns, or `unwrap()`
/// - fold warning accumulation into higher-level `Warnable` return values
///
/// # When **not** to use it
///
/// - when you need the returned value
/// - when failure should abort the computation
/// - when full error handling is required
///
/// # Examples
///
/// ## Ignoring a `Result` but recording a warning
/// ```ignore
/// use trywarn::StdErrLogger;
/// use trywarn::Trivialize;
/// fn do_side_effect() -> Result<(), String>;
///
/// let log = StdErrLogger;
///
/// do_side_effect().trivialize(log); // any Err becomes a warning
/// ```
///
/// ## Ignoring an `Option` but noting absence
/// ```rust
/// use trywarn::StdErrLogger;
/// use trywarn::Trivialize;
/// fn maybe_fetch() -> Option<u32> { None }
///
/// let warnable = maybe_fetch().trivialize(StdErrLogger);
///
/// if !warnable.is_empty() {
///     println!("a value was expected but missing");
/// }
/// ```
///
/// ## Integrating with a function that returns `Warnable`
/// ```ignore
/// use trywarn::{Warnable, StdErrLogger};
/// use trywarn::Trivialize;
/// fn step1() -> Result<(), String> { Err("trivial".into()) }
/// fn step2() -> Result<(), String> { Ok(()) }
///
/// fn process() -> Warnable<(), String, StdErrLogger> {
///     let log = StdErrLogger;
///
///     let mut w = step1().trivialize(log);
///     w.merge(step2().trivialize(log));
///
///     w
/// }
/// ```
///
/// # Notes
///
/// - `trivialize` always returns `Warnable<(), W, L>`
/// - No panics occur
/// - No short-circuiting happens
///
/// # See also
///
/// - [`Warnable`]
/// - [`Logger`]
/// - methods like `merge()` for accumulating warnings
#[cfg_attr(not(debug_assertions), deprecated(
    note = "`trivialize` should not be used in production builds"
))]
pub trait Trivialize<W, L>
where
    W: std::error::Error + Send + Sync + 'static,
    L: Logger<W> + 'static,
{
    /// Convert this value into a `Warnable<(), W, L>`, discarding the original
    /// value while optionally recording a warning derived from it.
    ///
    /// See trait-level documentation for full behavior.
    fn trivialize(self, logger: L) -> Warnable<(), W, L>;
}

impl<T, W, L> Trivialize<W, L> for Result<T, W>
where
    W: std::error::Error + Send + Sync + 'static,
    L: Logger<W> + 'static,
{
    fn trivialize(self, logger: L) -> Warnable<(), W, L> {
        if !cfg!(debug_assertions) {
            eprintln!("warning: `trivialize` used in release build — this may hide errors");
        }
        match self {
            Ok(_) => Warnable::clear((), logger),
            Err(w) => {
                Warnable::warning((), w, logger)
            }
        }
    }
}

/// A warning used to construct a `Warnable` from an `Option`
#[derive(Debug)]
pub struct NoneWarning;

impl std::error::Error for NoneWarning {}
impl std::fmt::Display for NoneWarning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "uninitialized or null value from Option")
    }
}

impl<T, L> Trivialize<NoneWarning, L> for Option<T>
where
    L: Logger<NoneWarning> + 'static,
{
    fn trivialize(self, logger: L) -> Warnable<(), NoneWarning, L> {
        if !cfg!(debug_assertions) {
            eprintln!("warning: `trivialize` used in release build — this may hide errors");
        }
        match self {
            Some(_) => Warnable::clear((), logger),
            None => {
                Warnable::warning((), NoneWarning, logger)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug)]
    struct DummyWarning(&'static str);

    impl fmt::Display for DummyWarning {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    impl std::error::Error for DummyWarning {}

    #[test]
    fn test_warnable_propagate() {
        let wrapped = Warnable::new(10, Some(DummyWarning("warning 1")), StdErrLogger);
        let value = wrapped.unwrap();
        assert_eq!(value, 10);
    }

    #[test]
    fn test_warnable_hide() {
        let wrapped = Warnable::new(20, Some(DummyWarning("warning 2")), StdErrLogger);
        let value = wrapped.hide();
        assert_eq!(value, 20);
    }

    #[test]
    fn test_warnable_clear_and_warn() {
        let cleared = Warnable::<i32, DummyWarning, StdErrLogger>::clear(100, StdErrLogger);
        assert_eq!(cleared.hide(), 100);

        let warned: Warnable<i32, DummyWarning, StdErrLogger> = Warnable::warning(200, DummyWarning("warning 3"), StdErrLogger);
        assert_eq!(warned.unwrap(), 200);
    }

    #[test]
    fn test_warnable_debug_format() {
        let wrapped = Warnable::new(42, Some(DummyWarning("debug warning")), StdErrLogger);
        let s = format!("{:?}", wrapped);
        assert!(s.contains("value"));
        assert!(s.contains("warnings"));
    }
}