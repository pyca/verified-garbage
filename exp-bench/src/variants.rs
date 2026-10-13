variant!(xs_cur, "../variants/xs_cur.s");
variant!(xs_cur_raw, "../variants/xs_cur_raw.s");
variant!(xs_notri, "../variants/xs_notri.s");
variant!(xs_norows, "../variants/xs_norows.s");
variant!(xs_nodiag, "../variants/xs_nodiag.s");
fn variants() -> Vec<(&'static str, F)> { vec![("main + xmm6/7", xs_cur), ("only raw of main", xs_cur_raw), ("only raw, no triangles", xs_notri), ("only raw, no rect rows", xs_norows), ("only raw, no diagonal", xs_nodiag)] }
