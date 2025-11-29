//! Using `trivialize` to convert Result/Option into Warnable
use trywarn::{StdErrLogger, Trivialize, Warnable, DefaultWarning};

fn may_fail(i: i32) -> Result<i32, DefaultWarning> {
    if i % 2 == 0 {
        Ok(i)
    } else {
        Err(DefaultWarning::from("odd number"))
    }
}

fn main() {
    let logger = StdErrLogger;

    // Trivialize a Result
    let w: Warnable<(), DefaultWarning, _> = may_fail(3).trivialize(logger);

    println!("Trivialized Result has warnings? {}", !w.warnings().is_empty());

    // Trivialize an Option
    let none_option: Option<i32> = None;
    let w2 = none_option.trivialize(logger);

    println!("Trivialized Option has warnings? {}", !w2.warnings().is_empty());
}
