variant!(xs_cur, "../variants/xs_cur.s");
variant!(xs_ssesel, "../variants/xs_ssesel.s");
variant!(xs_nosub, "../variants/xs_nosub.s");
variant!(xs_nosel, "../variants/xs_nosel.s");
fn variants() -> Vec<(&'static str, F)> { vec![("main + xmm6/7", xs_cur), ("select by SSE masks", xs_ssesel), ("only raw+redc, no final sub", xs_nosub), ("only raw+redc+sub, no select", xs_nosel)] }
