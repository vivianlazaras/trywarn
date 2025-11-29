use std::ops::{ControlFlow, Try, FromResidual};
use crate::{Logger, Warnable};

impl<T, W, L> FromResidual for Warnable<T, W, L> 
    where W: std::error::Error + 'static + Send + Sync,
        L: Logger<W> + 'static + Send + Sync,
{
    fn from_residual(residual: Self) -> Self {
        residual
    }
}

impl<T, W, L> Try for Warnable<T, W, L>
where
    W: std::error::Error + Send + Sync + 'static,
    L: Logger<W> + 'static,
{
    type Output = T;
    type Residual = Self;

    fn from_output(_output: Self::Output) -> Self {
        // No warning
        panic!("from_output should not be called directly; Warnable always has a logger")
    }

    #[track_caller]
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        ControlFlow::Continue(self.unwrap())
    }
}