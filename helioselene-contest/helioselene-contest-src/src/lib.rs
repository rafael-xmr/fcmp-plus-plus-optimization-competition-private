#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![doc = include_str!("../README.md")]
#![no_std]

pub use group;

#[macro_use]
mod backend;

mod field;
pub use field::{HeliosField as Field25519, SeleneField};

mod point;
pub use point::{HeliosPoint, SelenePoint};
