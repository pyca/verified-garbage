variant!(o0, "../variants/o0.s");
variant!(m0, "../variants/m0.s");
variant!(m_ld, "../variants/m_ld.s");
variant!(m_ld2, "../variants/m_ld2.s");
variant!(r16, "../variants/r16.s");
variant!(o_raw, "../variants/o_raw.s");
variant!(c_raw, "../variants/c_raw.s");
variant!(c_redc, "../variants/c_redc.s");
fn variants() -> Vec<(&'static str, F)> { vec![("old rotate8", o0), ("row8 (#1685)", m0), ("row8 sep load", m_ld), ("row8 sep load early", m_ld2), ("row16 blk16", r16), ("old only raw", o_raw), ("row8 only raw", c_raw), ("row8 only raw+redc", c_redc)] }
