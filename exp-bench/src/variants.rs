variant!(main_k, "../variants/main.s");
variant!(cur_k, "../variants/cur.s");
variant!(cur_raw, "../variants/cur_raw.s");
fn variants() -> Vec<(&'static str, F)> { vec![("main", main_k), ("PRs 1743+1749", cur_k), ("only raw of PRs", cur_raw)] }
