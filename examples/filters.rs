//! Using allow and deny filters to control warning propagation
use trywarn::{Warnable, DefaultWarning, StdErrLogger};

fn main() {
    let value = 10;

    // Initial warnable with one warning
    let mut w = Warnable::warning(value, DefaultWarning::from("first warning"), StdErrLogger);

    // Add more warnings
    w.warn("second warning");
    w.warn("third warning");

    // Allow warnings that contain "second"
    w = w.allow(|w: &DefaultWarning| w.as_ref().contains("second"));

    // Deny warnings that contain "third"
    w = w.deny(|w: &DefaultWarning| w.as_ref().contains("third"));

    // Convert to result; any denied warnings could produce Err
    let res = w.into_result();

    println!("Wrapped value with filters applied: {:?}", res);
}
