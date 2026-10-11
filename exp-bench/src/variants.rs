variant!(xs_cur, "../variants/xs_cur.s");
variant!(xs_fin2, "../variants/xs_fin2.s");
variant!(xs_ssesel, "../variants/xs_ssesel.s");
variant!(xs_nosub, "../variants/xs_nosub.s");
fn variants() -> Vec<(&'static str, F)> { vec![("main + xmm6/7", xs_cur), ("final step keeping CF (lea/dec)", xs_fin2), ("select by SSE masks", xs_ssesel), ("only raw+redc, no final sub", xs_nosub)] }
