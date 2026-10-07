import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafPrep

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64

/-- Recode both public scalars while retaining the first digit buffer. -/
theorem jointPrep_ok (c : Joint.Cfg) {s : State} {base : Addr} {size u v : Nat}
    (hs : Scr s base size) (hu : u+32≤size) (hu8 : u%8=0)
    (hv : v+32≤size) (hv8 : v%8=0)
    (hg : c.gBits<4096) (hg8 : c.gBits%8=0) (hgb : c.gBits+264≤size)
    (hq : c.K.bits<4096) (hq8 : c.K.bits%8=0) (hqb : c.K.bits+264≤size)
    (hsep : c.gBits+264≤c.K.bits ∨ c.K.bits+264≤c.gBits)
    (hvs : v+32≤c.gBits ∨ c.gBits+264≤v) :
    WP isa (.seq (Impl.Weierstrass.AArch64.FastNaf.prep c.G u 7)
      (Impl.Weierstrass.AArch64.FastNaf.prep c.K v 5)) s fun t =>
      Scr t base size ∧
      (∀ j<257,t.mem (off base (c.gBits+j))=FastNaf.byte 7 (wordsVal s.mem base u 4) j) ∧
      (∀ j<257,t.mem (off base (c.K.bits+j))=FastNaf.byte 5 (wordsVal s.mem base v 4) j) ∧
      KeepRegs nafPrepClob s t ∧ Unch base [(c.gBits,264),(c.K.bits,264)] s.mem t.mem := by
  refine WP.seq (WP.mono (fastPrep_ok c.G (Or.inr rfl) hs hu hu8 hg hg8 hgb)
    fun a ⟨pa,ka,oa⟩ => ?_)
  have va : wordsVal a.mem base v 4=wordsVal s.mem base v 4 :=
    oa.wordsVal hvs (by have := hs.nowrap; omega)
  refine WP.mono (fastPrep_ok c.K (Or.inl rfl) pa.scr hv hv8 hq hq8 hqb)
    fun t ⟨pt,kt,ot⟩ => ?_
  refine ⟨pt.scr,?_,?_,ka.trans kt,?_⟩
  · intro j hj
    rw [ot.unch.byte (by
      intro w hw; rw [List.mem_singleton.mp hw]; dsimp only; omega)
      (by have := hs.nowrap; omega)]
    exact pa.digits j hj
  · rw [va] at pt
    exact pt.digits
  · exact oa.unch.trans ot.unch

end VG.Proof.Weierstrass.AArch64
