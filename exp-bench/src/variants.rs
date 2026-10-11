variant!(xs_cur, "../variants/xs_cur.s");
variant!(xs_cur_raw, "../variants/xs_cur_raw.s");
variant!(xs_imul, "../variants/xs_imul.s");
fn variants() -> Vec<(&'static str, F)> { vec![("main + xmm6/7", xs_cur), ("only raw of main + xmm6/7", xs_cur_raw), ("q by imul", xs_imul)] }
