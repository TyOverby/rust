// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.



trait to_str {
    fn to_string(&self) -> StrBuf;
}

impl to_str for int {
    fn to_string(&self) -> StrBuf { self.to_str().to_strbuf() }
}

impl<T:to_str> to_str for Vec<T> {
    fn to_string(&self) -> StrBuf {
        format_strbuf!("[{}]",
                       self.iter()
                           .map(|e| e.to_string())
                           .collect::<Vec<StrBuf>>()
                           .connect(", "))
    }
}

pub fn main() {
    assert!(1.to_string() == "1".to_strbuf());
    assert!((vec!(2, 3, 4)).to_string() == "[2, 3, 4]".to_strbuf());

    fn indirect<T:to_str>(x: T) -> StrBuf {
        format_strbuf!("{}!", x.to_string())
    }
    assert!(indirect(vec!(10, 20)) == "[10, 20]!".to_strbuf());

    fn indirect2<T:to_str>(x: T) -> StrBuf {
        indirect(x)
    }
    assert!(indirect2(vec!(1)) == "[1]!".to_strbuf());
}
