// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(managed_boxes)]

// error-pattern:fail

fn main() {
    let cheese = "roquefort".to_strbuf();
    let carrots = @"crunchy".to_strbuf();

    let result: |@StrBuf, |StrBuf||: 'static = (|tasties, macerate| {
        macerate((*tasties).clone());
    });
    result(carrots, |food| {
        let mush = format_strbuf!("{}{}", food, cheese);
        let cheese = cheese.clone();
        let f: || = || {
            let _chew = format_strbuf!("{}{}", mush, cheese);
            fail!("so yummy")
        };
        f();
    });
}
