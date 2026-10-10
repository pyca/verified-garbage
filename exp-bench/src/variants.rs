variant!(o0, "../variants/o0.s");
variant!(o_diag8, "../variants/o_diag8.s");
variant!(o_raw, "../variants/o_raw.s");
variant!(c_rect, "../variants/c_rect.s");
fn variants() -> Vec<(&'static str, F)> { vec![("old rotate8", o0), ("diag 8-word groups", o_diag8), ("only raw", o_raw), ("only rect", c_rect)] }
