variant!(o0, "../variants/o0.s");
variant!(n_ends, "../variants/n_ends.s");
variant!(o_raw, "../variants/o_raw.s");
variant!(n_raw, "../variants/n_raw.s");
variant!(o_redc, "../variants/o_redc.s");
fn variants() -> Vec<(&'static str, F)> { vec![("old rotate8", o0), ("block ends, no zeroing", n_ends), ("only old raw", o_raw), ("only ends raw", n_raw), ("only old raw+redc", o_redc)] }
