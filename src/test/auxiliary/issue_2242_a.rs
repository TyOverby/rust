// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![crate_id="a#0.1"]
#![crate_type = "lib"]

trait to_strz {
    fn to_strz() -> StrBuf;
}

impl to_strz for StrBuf {
    fn to_strz() -> StrBuf { self.clone() }
}
