import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafLoop

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont

/-- Both measured public widths produce all257 signed digits, touching only their264-byte buffer. -/
theorem fastPrep_ok (K : WinCfg) {w : Nat} (hw : FastNaf.Width w)
    {s : State} {base : Addr} {size src : Nat}
    (hs : Scr s base size) (hsrc : src+32≤size) (hsrc8 : src%8=0)
    (hbits : K.bits<4096) (hbits8 : K.bits%8=0) (hb : K.bits+264≤size) :
    WP isa (Impl.Weierstrass.AArch64.FastNaf.prep K src w) s fun t =>
      FastPrepPost base size K.bits w (wordsVal s.mem base src 4) t ∧
      KeepRegs nafPrepClob s t ∧ Outside base K.bits 264 s.mem t.mem := by
  rw [Impl.Weierstrass.AArch64.FastNaf.prep]
  refine WP.seq (WP.mono (fastSetup_ok K hw hs hsrc hsrc8 hbits hbits8 hb) fun a ⟨ia,ka,oa⟩ => ?_)
  refine WP.mono (fastLoop_ok ia hw (wordsVal_lt ..) hb (by decide)) fun t ⟨it,kt,ot⟩ => ?_
  exact ⟨it,ka.trans (kt.mono (by decide)),oa.trans ot⟩

end VG.Proof.Weierstrass.AArch64
