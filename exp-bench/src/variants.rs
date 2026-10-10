variant!(o0, "../variants/o0.s");
variant!(o_imul, "../variants/o_imul.s");
variant!(m0, "../variants/m0.s");
variant!(r16, "../variants/r16.s");
variant!(o_raw, "../variants/o_raw.s");
variant!(o_redc, "../variants/o_redc.s");
variant!(o_nochain, "../variants/o_nochain.s");
fn variants() -> Vec<(&'static str, F)> { vec![("old rotate8", o0), ("old imul u", o_imul), ("row8 (#1685)", m0), ("row16 blk16", r16), ("old only raw", o_raw), ("old only raw+redc", o_redc), ("only old no u-chain", o_nochain)] }
