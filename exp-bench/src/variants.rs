variant!(xs_cur, "../variants/xs_cur.s");
variant!(xs_cur_raw, "../variants/xs_cur_raw.s");
variant!(xs_nosub, "../variants/xs_nosub.s");
fn variants() -> Vec<(&'static str, F)> { vec![("main + xmm6/7", xs_cur), ("only raw of main + xmm6/7", xs_cur_raw), ("only raw+redc, no final sub", xs_nosub)] }
