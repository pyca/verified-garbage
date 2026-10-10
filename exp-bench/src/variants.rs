variant!(o0, "../variants/o0.s");
variant!(c_zero, "../variants/c_zero.s");
variant!(c_tri, "../variants/c_tri.s");
variant!(c_rect, "../variants/c_rect.s");
variant!(o_raw, "../variants/o_raw.s");
variant!(o_redc, "../variants/o_redc.s");
fn variants() -> Vec<(&'static str, F)> { vec![("old rotate8", o0), ("only zero", c_zero), ("only tri", c_tri), ("only rect", c_rect), ("only raw", o_raw), ("only raw+redc", o_redc)] }
