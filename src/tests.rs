use std::{io::Write, path::PathBuf, str::FromStr};

use crate::{
    error_reporting::{report_error, IErr},
    syntax::{Eff, SExpr, Type},
    typecheck,
};

pub fn typecheck_(src: &str, src_path: &str) -> Result<(SExpr, Type, Eff), IErr> {
    typecheck(src, false).map_err(|e| {
        report_error(src_path, &src, e.clone());
        e
    })
}

macro_rules! logln {
    ($($args:tt)*) => {
        writeln!(::std::io::stdout(), $($args)*).unwrap()
    };
}

#[test]
fn unit_tests() {
    let positives: Vec<PathBuf> = std::fs::read_dir("examples/positive")
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .collect();
    let negatives: Vec<PathBuf> = std::fs::read_dir("examples/negative")
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .collect();
    let mut failures_pos = vec![];
    for (i, p) in positives.iter().enumerate() {
        let name = p.to_string_lossy().to_string();
        logln!(
            "\n================================================================================"
        );
        logln!(
            "Running positive test {} / {}: {}\n",
            i + 1,
            positives.len(),
            name
        );
        let src = std::fs::read_to_string(p).unwrap();
        let res = typecheck_(&src, &name);
        if res.is_ok() {
            logln!("TEST SUCCEEDED.")
        } else {
            logln!("TEST FAILED.");
            failures_pos.push(name.clone())
        }
    }
    let mut failures_neg = vec![];
    for (i, p) in negatives.iter().enumerate() {
        let name = p.to_string_lossy().to_string();
        logln!(
            "\n================================================================================"
        );
        logln!(
            "Running negative test {} / {}: {}\n",
            i + 1,
            negatives.len(),
            name
        );
        let src = std::fs::read_to_string(p).unwrap();
        let res = typecheck_(&src, &name);
        if res.is_err() {
            logln!("TEST SUCCEEDED.")
        } else {
            logln!("TEST FAILED.");
            failures_neg.push(name.clone())
        }
    }
    logln!("\n================================================================================\n");
    if failures_pos.len() == 0 && failures_neg.len() == 0 {
        logln!("ALL {} TESTS PASSED!", positives.len() + negatives.len())
    } else {
        logln!(
            "{} TESTS FAILED:\n",
            failures_neg.len() + failures_pos.len()
        );
        for n in failures_neg {
            logln!("  {n}")
        }
        for n in failures_pos {
            logln!("  {n}")
        }
        assert!(false)
    }
}
