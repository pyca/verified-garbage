variant!(xs_cur, "../variants/xs_cur.s");
variant!(xs_al5, "../variants/xs_al5.s");
variant!(xs_al6, "../variants/xs_al6.s");
variant!(xs_noptail, "../variants/xs_noptail.s");
variant!(xs_noptail_al5, "../variants/xs_noptail_al5.s");
variant!(xs_lazy, "../variants/xs_lazy.s");
fn variants() -> Vec<(&'static str, F)> { vec![("main + xmm6/7", xs_cur), ("loop heads aligned to 32", xs_al5), ("loop heads aligned to 64", xs_al6), ("product rows store their carry", xs_noptail), ("product carry store + loops aligned to 32", xs_noptail_al5), ("only: lazy final step (masked subtraction)", xs_lazy)] }
