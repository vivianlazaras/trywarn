# Try Warn
This crate provides a means of propagating non critical warning states, backed by an underlying Logger implementation to control when warnings are logged, ignored, or a fatal issue when the priorities of a crate developer, and a crate's user aren't aligned on what they consider critical error, or acceptable warnings.

The goal of this crate is also to distinguish debug, and release builds in terms of warning and error severity to allow for more rapid prototyping without compromising quality of code in release builds, and hopefully helping to deminish the learning curve of rust a bit (similar to the motivations behind anyhow).

## How it works:

This crate provides the `Warnable` type, a wrapper around a value that may
have associated non-fatal warnings. The warnings can be automatically logged
via a `Logger` implementation, propagated manually, or ignored.  

Features:
- Attach warnings to a value without failing.
- Automatic logging in debug builds and in `Drop`.
- Optional manual propagation of warnings via `propagate()` or `unwrap()`.
- Works with custom logging mechanisms.

### Macro Example

```rust
use trywarn::{warn, warninit, ret};
use std::fmt;

#[derive(Debug)]
struct MyWarning(&'static str);

impl fmt::Display for MyWarning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for MyWarning {}

let mut warning = warninit!(String, MyWarning);
warn!(warning, MyWarning("hello world"));
// only shows the warning/info message on debug builds
info!(warning, MyWarning("Some good info to have"), true);
let warnable = ret!(warnings, "hello world".to_string());
// unwraps logging any warnings to StdErr (default logger).
let message = warnable.unwrap();
```

### Manual Example

```rust
use trywarn::{Warnable, StdErrLogger};
use std::fmt;

#[derive(Debug)]
struct MyWarning(&'static str);

impl fmt::Display for MyWarning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for MyWarning {}

let wrapped = Warnable::warning(42, MyWarning("minor issue"), StdErrLogger);
let value = wrapped.unwrap(); // logs warning and returns 42
assert_eq!(value, 42);
```

## Future Plans
1. Handle logger trait error handling cleanly.
2. Move unwrap to flush, implement unwrap as a panic fn.
3. Implement expect.