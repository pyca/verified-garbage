variant!(xs_cur, "../variants/xs_cur.s");
variant!(xs_roll, "../variants/xs_roll.s");
fn variants() -> Vec<(&'static str, F)> { vec![("main + xmm6/7", xs_cur), ("rect tile rows rolled", xs_roll)] }
