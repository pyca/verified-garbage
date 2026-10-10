variant!(o0, "../variants/o0.s");
variant!(o_diag8, "../variants/o_diag8.s");
variant!(b_nozero, "../variants/b_nozero.s");
variant!(b_nohead, "../variants/b_nohead.s");
fn variants() -> Vec<(&'static str, F)> { vec![("old rotate8", o0), ("diag 8-word groups", o_diag8), ("only no zeroing", b_nozero), ("only tri no row address", b_nohead)] }
