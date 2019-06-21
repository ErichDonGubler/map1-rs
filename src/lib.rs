//! This crate houses several wrappers and convenience macros over `std` collections that guarantee
//! that they will never be empty. This is particularly useful for modeling APIs and data that need
//! a non-empty invariant and reducing potential error cases by using types rather than
//! conventions.
//!
//! The crate provides an optional serde feature, which provides implementations of
//! `serde::Serialize`/`serde::Deserialize`.

#![cfg_attr(not(debug_assertions), deny(warnings))]
#![doc(html_playground_url = "https://play.rust-lang.org/")]
#![doc(test(attr(deny(warnings))))]
#![doc(test(attr(warn(
    bare_trait_objects,
    clippy::cargo,
    clippy::pedantic,
    elided_lifetimes_in_paths,
    missing_copy_implementations,
    single_use_lifetimes,
))))]
#![warn(
    bare_trait_objects,
    clippy::cargo,
    clippy::pedantic,
    elided_lifetimes_in_paths,
    missing_copy_implementations,
    missing_docs,
    single_use_lifetimes,
    unused_extern_crates
)]
#![allow(clippy::multiple_crate_versions)]

pub mod btree_map;
pub use btree_map::BTreeMap1;

#[test]
fn check_readme_synchronized() {
    use {
        cargo_sync_readme::{extract_inner_doc, read_readme, transform_readme},
        std::path::PathBuf,
    };

    let crate_docs = extract_inner_doc(file!(), false, cfg!(windows));
    let readme_path = PathBuf::from(file!())
        .parent()
        .and_then(|p| p.parent())
        .expect("unable to create path to README dir")
        .join("README.md");
    let current_readme_content = read_readme(readme_path).expect("unable to read README");
    if transform_readme(&current_readme_content, crate_docs, cfg!(windows)).unwrap()
        != current_readme_content
    {
        panic!("README is not sync'd -- make sure to run `cargo sync-readme`");
    }
}
