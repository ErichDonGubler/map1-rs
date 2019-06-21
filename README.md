# New Rust Project

<!-- NOTE: You can also use a Crates.io version of this license badge: https://shields.io/category/license -->
[![License](https://img.shields.io/github/license/erichdongubler/map1-rs.svg)](LICENSE.md)
[![Crates.io](https://img.shields.io/crates/v/map1.svg)](https://crates.io/crates/map1)
[![Docs.rs](https://docs.rs/map1/badge.svg)](https://docs.rs/map1)
[![Matrix chat](https://img.shields.io/matrix/map1-rs:matrix.org.svg)](https://matrix.to/#/#map1-rs:matrix.org)

[![last release date](https://img.shields.io/github/release-date/erichdongubler/map1-rs.svg)](https://github.com/erichdongubler/map1-rs/releases)
[![repo activity](https://img.shields.io/github/commit-activity/m/erichdongubler/map1-rs.svg)](https://github.com/erichdongubler/map1-rs/pulse/monthly)
[![contributors](https://img.shields.io/github/contributors/erichdongubler/map1-rs.svg)](https://github.com/erichdongubler/map1-rs/graphs/contributors)
[![Build Status](https://secure.travis-ci.org/erichdongubler/map1-rs.svg?branch=master)](https://travis-ci.org/erichdongubler/map1-rs)

<!-- cargo-sync-readme start -->

This crate houses several wrappers and convenience macros over `std` collections that guarantee
that they will never be empty. This is particularly useful for modeling APIs and data that need
a non-empty invariant and reducing potential error cases by using types rather than
conventions.

The crate provides an optional serde feature, which provides implementations of
`serde::Serialize`/`serde::Deserialize`.

<!-- cargo-sync-readme end -->
