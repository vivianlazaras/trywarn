/// Initializes a warning tracking context in the current scope.
///
/// Returns a `Warnable<Option<T>>` which can accumulate warnings.
/// Must be used with `warn!(warnable, ...)` and `ret!(warnable, ...)`.
#[macro_export]
macro_rules! warninit {
    // With explicit type, explicit warning type, and logger
    ($ty:ty, $warn:ty, $logger:expr) => {
        $crate::Warnable::<Option<$ty>, $warn, L>::new_uninitialized($logger, false)
    };

    ($ty:ty, $warn:ty) => {
        $crate::Warnable::<Option<$ty>, $warn>::new_uninitialized($crate::DefaultLogger::default(), false)
    };

    // With explicit type and logger (default warning type)
    ($ty:ty, $logger:expr) => {
        $crate::Warnable::<Option<$ty>, DefaultWarning, L>::new_uninitialized($logger, false)
    };

    // With explicit type only (use DefaultWarning + DefaultLogger)
    ($ty:ty) => {
        $crate::Warnable::<Option<$ty>, $crate::DefaultWarning>::new_uninitialized(
            $crate::DefaultLogger::default(),
            false,
        )
    };

    // No type, custom logger → use DefaultWarning
    ($logger:expr) => {
        $crate::Warnable::<Option<()>, $crate::DefaultWarning>::new_uninitialized(
            $logger,
            false,
        )
    };

    // No arguments → default type + logger
    () => {
        $crate::Warnable::<Option<()>, $crate::DefaultWarning>::new_uninitialized(
            $crate::DefaultLogger::default(),
            false,
        )
    };
}

/// Records a warning in a given Warnable
#[macro_export]
macro_rules! warn {
    ($warnable:expr, $warning:expr) => {{
        $warnable.warn($warning);
    }};

    ($warnable:expr, $warning:expr, $dbg:literal) => {{
        $warnable.dbgwarn($warning, $dbg);
    }};

    // == operator  (warn when false)
    ($warnable:expr, $cond:expr, $warning:expr) => {{
        if !$cond {
            $warnable.warn($warning);
        }
    }};

    // == operator  (warn when false)
    ($warnable:expr, $cond:expr, $warning:expr, $dbg:literal) => {{
        if !$cond {
            $warnable.dbgwarn($warning, $dbg);
        }
    }};
}

/// Records a message in a given Warnable
#[macro_export]
macro_rules! info {
    ($warnable:expr, $warning:expr) => {{
        $warnable.info($warning);
    }};

    ($warnable:expr, $warning:expr, $dbg:literal) => {{
        $warnable.dbginfo($warning, $dbg);
    }};

    // == operator  (warn when false)
    ($warnable:expr, $cond:expr, $warning:expr) => {{
        if !$cond {
            $warnable.info($warning);
        }
    }};

    // == operator  (warn when false)
    ($warnable:expr, $cond:expr, $warning:expr, $dbg:literal) => {{
        if !$cond {
            $warnable.dbginfo($warning, $dbg);
        }
    }};

}

/// Returns the value from a Warnable and propagates any accumulated warnings
#[macro_export]
macro_rules! ret {
    ($warnable:expr, $value:expr) => {{
        $warnable.set_value($value).unoptionize()
    }};
}