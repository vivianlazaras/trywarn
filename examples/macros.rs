//! Example using trywarn macros (warninit!, ret!, etc.)
use trywarn::{warninit, warn, info, ret, Warnable, StdErrLogger, DefaultWarning};

fn main() {
    // Create a Warnable using warninit! macro
    let mut w: Warnable<Option<i32>, DefaultWarning, StdErrLogger> = warninit!(i32, DefaultWarning, StdErrLogger);
    warn!(w, "another warning");
    info!(w, "an informative message");
    // Merge with another Warnable using ret! macro
    let other = ret!(w.clone(), 100);

    let neww = w.clone().set_value(100);
    let merged_value = neww.clone().unoptionize().merge(&mut other.clone());
    println!("Merged value: {}", merged_value);

    // Unwrap to see warnings printed
    let final_value = neww.unwrap().unwrap();
    println!("Final value: {}", final_value);
    assert_eq!(merged_value, final_value);
}