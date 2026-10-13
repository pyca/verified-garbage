variant!(xs_cur, "../variants/xs_cur.s");
variant!(xs_lazy, "../variants/xs_lazy.s");
variant!(xs_nosub, "../variants/xs_nosub.s");
variant!(xs_noptail, "../variants/xs_noptail.s");
variant!(xs_notail, "../variants/xs_notail.s");
fn variants() -> Vec<(&'static str, F)> { vec![("main + xmm6/7", xs_cur), ("only: lazy final step (masked subtraction)", xs_lazy), ("only raw+redc, no final sub", xs_nosub), ("product rows store their carry", xs_noptail), ("only: square without the rows' tail", xs_notail)] }
