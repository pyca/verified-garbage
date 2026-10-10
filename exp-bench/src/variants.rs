variant!(o0, "../variants/o0.s");
variant!(n_ends, "../variants/n_ends.s");
variant!(t_ossl, "../variants/t_ossl.s");
fn variants() -> Vec<(&'static str, F)> { vec![("old rotate8", o0), ("block ends, no zeroing", n_ends), ("only openssl triangle", t_ossl)] }
