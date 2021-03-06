// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![crate_type = "bin"]
#![feature(phase)]

// we use our own (green) start below; do not link in libnative; issue #13247.
#![no_start]

#![deny(warnings)]

extern crate test;
extern crate getopts;
#[phase(link, syntax)]
extern crate log;
extern crate green;
extern crate rustuv;

extern crate regex;

use std::os;
use std::io;
use std::io::fs;
use std::from_str::FromStr;
use getopts::{optopt, optflag, reqopt};
use common::Config;
use common::{Pretty, DebugInfoGdb, Codegen};
use util::logv;

pub mod procsrv;
pub mod util;
pub mod header;
pub mod runtest;
pub mod common;
pub mod errors;

#[start]
fn start(argc: int, argv: **u8) -> int {
    green::start(argc, argv, rustuv::event_loop, main)
}

pub fn main() {
    let args = os::args();
    let config = parse_config(args.move_iter()
                                  .map(|x| x.to_strbuf())
                                  .collect());
    log_config(&config);
    run_tests(&config);
}

pub fn parse_config(args: Vec<StrBuf> ) -> Config {

    let groups : Vec<getopts::OptGroup> =
        vec!(reqopt("", "compile-lib-path", "path to host shared libraries", "PATH"),
          reqopt("", "run-lib-path", "path to target shared libraries", "PATH"),
          reqopt("", "rustc-path", "path to rustc to use for compiling", "PATH"),
          optopt("", "clang-path", "path to  executable for codegen tests", "PATH"),
          optopt("", "llvm-bin-path", "path to directory holding llvm binaries", "DIR"),
          reqopt("", "src-base", "directory to scan for test files", "PATH"),
          reqopt("", "build-base", "directory to deposit test outputs", "PATH"),
          reqopt("", "aux-base", "directory to find auxiliary test files", "PATH"),
          reqopt("", "stage-id", "the target-stage identifier", "stageN-TARGET"),
          reqopt("", "mode", "which sort of compile tests to run",
                 "(compile-fail|run-fail|run-pass|pretty|debug-info)"),
          optflag("", "ignored", "run tests marked as ignored"),
          optopt("", "runtool", "supervisor program to run tests under \
                                 (eg. emulator, valgrind)", "PROGRAM"),
          optopt("", "host-rustcflags", "flags to pass to rustc for host", "FLAGS"),
          optopt("", "target-rustcflags", "flags to pass to rustc for target", "FLAGS"),
          optflag("", "verbose", "run tests verbosely, showing all output"),
          optopt("", "logfile", "file to log test execution to", "FILE"),
          optopt("", "save-metrics", "file to save metrics to", "FILE"),
          optopt("", "ratchet-metrics", "file to ratchet metrics against", "FILE"),
          optopt("", "ratchet-noise-percent",
                 "percent change in metrics to consider noise", "N"),
          optflag("", "jit", "run tests under the JIT"),
          optopt("", "target", "the target to build for", "TARGET"),
          optopt("", "host", "the host to build for", "HOST"),
          optopt("", "android-cross-path", "Android NDK standalone path", "PATH"),
          optopt("", "adb-path", "path to the android debugger", "PATH"),
          optopt("", "adb-test-dir", "path to tests for the android debugger", "PATH"),
          optopt("", "lldb-python-dir", "directory containing LLDB's python module", "PATH"),
          optopt("", "test-shard", "run shard A, of B shards, worth of the testsuite", "A.B"),
          optflag("h", "help", "show this message"));

    assert!(!args.is_empty());
    let argv0 = (*args.get(0)).clone();
    let args_ = args.tail();
    if args.get(1).as_slice() == "-h" || args.get(1).as_slice() == "--help" {
        let message = format!("Usage: {} [OPTIONS] [TESTNAME...]", argv0);
        println!("{}", getopts::usage(message, groups.as_slice()));
        println!("");
        fail!()
    }

    let matches =
        &match getopts::getopts(args_.as_slice(), groups.as_slice()) {
          Ok(m) => m,
          Err(f) => fail!("{}", f.to_err_msg())
        };

    if matches.opt_present("h") || matches.opt_present("help") {
        let message = format!("Usage: {} [OPTIONS]  [TESTNAME...]", argv0);
        println!("{}", getopts::usage(message, groups.as_slice()));
        println!("");
        fail!()
    }

    fn opt_path(m: &getopts::Matches, nm: &str) -> Path {
        Path::new(m.opt_str(nm).unwrap())
    }

    let filter = if !matches.free.is_empty() {
        let s = matches.free.get(0).as_slice();
        match regex::Regex::new(s) {
            Ok(re) => Some(re),
            Err(e) => {
                println!("failed to parse filter /{}/: {}", s, e);
                fail!()
            }
        }
    } else {
        None
    };

    Config {
        compile_lib_path: matches.opt_str("compile-lib-path")
                                 .unwrap()
                                 .to_strbuf(),
        run_lib_path: matches.opt_str("run-lib-path").unwrap().to_strbuf(),
        rustc_path: opt_path(matches, "rustc-path"),
        clang_path: matches.opt_str("clang-path").map(|s| Path::new(s)),
        llvm_bin_path: matches.opt_str("llvm-bin-path").map(|s| Path::new(s)),
        src_base: opt_path(matches, "src-base"),
        build_base: opt_path(matches, "build-base"),
        aux_base: opt_path(matches, "aux-base"),
        stage_id: matches.opt_str("stage-id").unwrap().to_strbuf(),
        mode: FromStr::from_str(matches.opt_str("mode")
                                       .unwrap()
                                       .as_slice()).expect("invalid mode"),
        run_ignored: matches.opt_present("ignored"),
        filter: filter,
        logfile: matches.opt_str("logfile").map(|s| Path::new(s)),
        save_metrics: matches.opt_str("save-metrics").map(|s| Path::new(s)),
        ratchet_metrics:
            matches.opt_str("ratchet-metrics").map(|s| Path::new(s)),
        ratchet_noise_percent:
            matches.opt_str("ratchet-noise-percent")
                   .and_then(|s| from_str::<f64>(s.as_slice())),
        runtool: matches.opt_str("runtool").map(|x| x.to_strbuf()),
        host_rustcflags: matches.opt_str("host-rustcflags")
                                .map(|x| x.to_strbuf()),
        target_rustcflags: matches.opt_str("target-rustcflags")
                                  .map(|x| x.to_strbuf()),
        jit: matches.opt_present("jit"),
        target: opt_str2(matches.opt_str("target").map(|x| x.to_strbuf())),
        host: opt_str2(matches.opt_str("host").map(|x| x.to_strbuf())),
        android_cross_path: opt_path(matches, "android-cross-path"),
        adb_path: opt_str2(matches.opt_str("adb-path")
                                  .map(|x| x.to_strbuf())),
        adb_test_dir: opt_str2(matches.opt_str("adb-test-dir")
                                      .map(|x| x.to_strbuf())),
        adb_device_status:
            "arm-linux-androideabi" ==
                opt_str2(matches.opt_str("target")
                                .map(|x| x.to_strbuf())).as_slice() &&
            "(none)" !=
                opt_str2(matches.opt_str("adb-test-dir")
                                .map(|x| x.to_strbuf())).as_slice() &&
            !opt_str2(matches.opt_str("adb-test-dir")
                             .map(|x| x.to_strbuf())).is_empty(),
        lldb_python_dir: matches.opt_str("lldb-python-dir")
                                .map(|x| x.to_strbuf()),
        test_shard: test::opt_shard(matches.opt_str("test-shard")
                                           .map(|x| x.to_strbuf())),
        verbose: matches.opt_present("verbose")
    }
}

pub fn log_config(config: &Config) {
    let c = config;
    logv(c, format_strbuf!("configuration:"));
    logv(c, format_strbuf!("compile_lib_path: {}", config.compile_lib_path));
    logv(c, format_strbuf!("run_lib_path: {}", config.run_lib_path));
    logv(c, format_strbuf!("rustc_path: {}", config.rustc_path.display()));
    logv(c, format_strbuf!("src_base: {}", config.src_base.display()));
    logv(c, format_strbuf!("build_base: {}", config.build_base.display()));
    logv(c, format_strbuf!("stage_id: {}", config.stage_id));
    logv(c, format_strbuf!("mode: {}", config.mode));
    logv(c, format_strbuf!("run_ignored: {}", config.run_ignored));
    logv(c, format_strbuf!("filter: {}",
                           opt_str(&config.filter
                                          .as_ref()
                                          .map(|re| {
                                              re.to_str().into_strbuf()
                                          }))));
    logv(c, format_strbuf!("runtool: {}", opt_str(&config.runtool)));
    logv(c, format_strbuf!("host-rustcflags: {}",
                           opt_str(&config.host_rustcflags)));
    logv(c, format_strbuf!("target-rustcflags: {}",
                           opt_str(&config.target_rustcflags)));
    logv(c, format_strbuf!("jit: {}", config.jit));
    logv(c, format_strbuf!("target: {}", config.target));
    logv(c, format_strbuf!("host: {}", config.host));
    logv(c, format_strbuf!("android-cross-path: {}",
                           config.android_cross_path.display()));
    logv(c, format_strbuf!("adb_path: {}", config.adb_path));
    logv(c, format_strbuf!("adb_test_dir: {}", config.adb_test_dir));
    logv(c, format_strbuf!("adb_device_status: {}",
                           config.adb_device_status));
    match config.test_shard {
        None => logv(c, "test_shard: (all)".to_strbuf()),
        Some((a,b)) => logv(c, format_strbuf!("test_shard: {}.{}", a, b))
    }
    logv(c, format_strbuf!("verbose: {}", config.verbose));
    logv(c, format_strbuf!("\n"));
}

pub fn opt_str<'a>(maybestr: &'a Option<StrBuf>) -> &'a str {
    match *maybestr {
        None => "(none)",
        Some(ref s) => s.as_slice(),
    }
}

pub fn opt_str2(maybestr: Option<StrBuf>) -> StrBuf {
    match maybestr {
        None => "(none)".to_strbuf(),
        Some(s) => s,
    }
}

pub fn run_tests(config: &Config) {
    if config.target.as_slice() == "arm-linux-androideabi" {
        match config.mode {
            DebugInfoGdb => {
                println!("arm-linux-androideabi debug-info \
                         test uses tcp 5039 port. please reserve it");
            }
            _ =>{}
        }

        //arm-linux-androideabi debug-info test uses remote debugger
        //so, we test 1 task at once.
        // also trying to isolate problems with adb_run_wrapper.sh ilooping
        os::setenv("RUST_TEST_TASKS","1");
    }

    let opts = test_opts(config);
    let tests = make_tests(config);
    // sadly osx needs some file descriptor limits raised for running tests in
    // parallel (especially when we have lots and lots of child processes).
    // For context, see #8904
    io::test::raise_fd_limit();
    let res = test::run_tests_console(&opts, tests.move_iter().collect());
    match res {
        Ok(true) => {}
        Ok(false) => fail!("Some tests failed"),
        Err(e) => {
            println!("I/O failure during tests: {}", e);
        }
    }
}

pub fn test_opts(config: &Config) -> test::TestOpts {
    test::TestOpts {
        filter: match config.filter {
            None => None,
            Some(ref filter) => Some(filter.clone()),
        },
        run_ignored: config.run_ignored,
        logfile: config.logfile.clone(),
        run_tests: true,
        run_benchmarks: true,
        ratchet_metrics: config.ratchet_metrics.clone(),
        ratchet_noise_percent: config.ratchet_noise_percent.clone(),
        save_metrics: config.save_metrics.clone(),
        test_shard: config.test_shard.clone(),
        nocapture: false,
    }
}

pub fn make_tests(config: &Config) -> Vec<test::TestDescAndFn> {
    debug!("making tests from {}",
           config.src_base.display());
    let mut tests = Vec::new();
    let dirs = fs::readdir(&config.src_base).unwrap();
    for file in dirs.iter() {
        let file = file.clone();
        debug!("inspecting file {}", file.display());
        if is_test(config, &file) {
            let t = make_test(config, &file, || {
                match config.mode {
                    Codegen => make_metrics_test_closure(config, &file),
                    _ => make_test_closure(config, &file)
                }
            });
            tests.push(t)
        }
    }
    tests
}

pub fn is_test(config: &Config, testfile: &Path) -> bool {
    // Pretty-printer does not work with .rc files yet
    let valid_extensions =
        match config.mode {
          Pretty => vec!(".rs".to_owned()),
          _ => vec!(".rc".to_owned(), ".rs".to_owned())
        };
    let invalid_prefixes = vec!(".".to_owned(), "#".to_owned(), "~".to_owned());
    let name = testfile.filename_str().unwrap();

    let mut valid = false;

    for ext in valid_extensions.iter() {
        if name.ends_with(*ext) { valid = true; }
    }

    for pre in invalid_prefixes.iter() {
        if name.starts_with(*pre) { valid = false; }
    }

    return valid;
}

pub fn make_test(config: &Config, testfile: &Path, f: || -> test::TestFn)
                 -> test::TestDescAndFn {
    test::TestDescAndFn {
        desc: test::TestDesc {
            name: make_test_name(config, testfile),
            ignore: header::is_test_ignored(config, testfile),
            should_fail: false
        },
        testfn: f(),
    }
}

pub fn make_test_name(config: &Config, testfile: &Path) -> test::TestName {

    // Try to elide redundant long paths
    fn shorten(path: &Path) -> StrBuf {
        let filename = path.filename_str();
        let p = path.dir_path();
        let dir = p.filename_str();
        format_strbuf!("{}/{}", dir.unwrap_or(""), filename.unwrap_or(""))
    }

    test::DynTestName(format_strbuf!("[{}] {}",
                                     config.mode,
                                     shorten(testfile)))
}

pub fn make_test_closure(config: &Config, testfile: &Path) -> test::TestFn {
    let config = (*config).clone();
    // FIXME (#9639): This needs to handle non-utf8 paths
    let testfile = testfile.as_str().unwrap().to_strbuf();
    test::DynTestFn(proc() {
        runtest::run(config, testfile)
    })
}

pub fn make_metrics_test_closure(config: &Config, testfile: &Path) -> test::TestFn {
    let config = (*config).clone();
    // FIXME (#9639): This needs to handle non-utf8 paths
    let testfile = testfile.as_str().unwrap().to_strbuf();
    test::DynMetricFn(proc(mm) {
        runtest::run_metrics(config, testfile, mm)
    })
}
