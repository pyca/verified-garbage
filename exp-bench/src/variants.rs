variant!(xs_base, "../variants/xs_base.s");
variant!(xs_new, "../variants/xs_new.s");
fn variants() -> Vec<(&'static str, F)> { vec![("PRs, header saved by the tiles", xs_base), ("header saved in xmm6/7", xs_new)] }
