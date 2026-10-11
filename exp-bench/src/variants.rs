variant!(cur_rx, "../variants/cur_rx.s");
variant!(cur_raw, "../variants/cur_raw.s");
variant!(cut_tail, "../variants/cut_tail.s");
variant!(cut_hdr, "../variants/cut_hdr.s");
fn variants() -> Vec<(&'static str, F)> { vec![("PRs, registers saved in xmm6-11", cur_rx), ("only raw of PRs", cur_raw), ("only raw, no tail propagation", cut_tail), ("only raw, no header save", cut_hdr)] }
