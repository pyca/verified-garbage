variant!(xs_cur, "../variants/xs_cur.s");
variant!(xs_notail, "../variants/xs_notail.s");
variant!(xs_cur_raw, "../variants/xs_cur_raw.s");
fn variants() -> Vec<(&'static str, F)> { vec![("main + xmm6/7", xs_cur), ("only: square without the rows' tail", xs_notail), ("only raw of main", xs_cur_raw)] }
