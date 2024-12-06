#![warn(
    clippy::if_not_else,
    clippy::default_trait_access,
    clippy::use_self,
    clippy::perf,
    clippy::large_types_passed_by_value
)]

pub mod atact;
mod bls381_helpers;
mod lagrange;
pub mod pedersen;
pub mod s3id;
pub mod tsw;

pub use bls381_helpers::Scalar;
