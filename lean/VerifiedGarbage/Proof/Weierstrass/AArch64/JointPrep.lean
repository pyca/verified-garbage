module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNaf9
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64

/-- The generator's digits of the scalar at `u`, in either width. -/
theorem jointGPrep_ok (c : Joint.Cfg) {s : State} {base : Addr} {size u : Nat}
    (hs : Scr s base size) (hu : u+32≤size) (hu8 : u%8=0)
    (hg : c.gBits<4096) (hg8 : c.gBits%8=0) (hgb : c.gBits+jointGSpan c≤size) :
    WP isa (Joint.gPrep c u) s fun t =>
      Scr t base size ∧
      (∀ j<jointGLen c,t.mem (off base (c.gBits+j))=jointGByte c (wordsVal s.mem base u 4) j) ∧
      KeepRegs nafPrepClob s t ∧ Outside base c.gBits (jointGSpan c) s.mem t.mem := by
  by_cases h9 : c.gw=9
  · have hspan : jointGSpan c=520 := by rw [jointGSpan,ite_eq_left h9]
    rw [hspan] at hgb ⊢
    rw [Joint.gPrep,ite_eq_left h9]
    refine WP.mono (fastPrep9_ok c.G hs hu hu8 hg hg8 hgb) fun t ⟨pt,kt,ot⟩ => ⟨pt.scr,?_,kt,ot⟩
    intro j hj
    rw [jointGLen,ite_eq_left h9] at hj
    rw [jointGByte,ite_eq_left h9]
    exact pt.digits j hj
  · have hspan : jointGSpan c=264 := by rw [jointGSpan,ite_eq_right h9]
    rw [hspan] at hgb ⊢
    rw [Joint.gPrep,ite_eq_right h9]
    refine WP.mono (fastPrep_ok c.G (Or.inr rfl) hs hu hu8 hg hg8 hgb) fun t ⟨pt,kt,ot⟩ => ⟨pt.scr,?_,kt,ot⟩
    intro j hj
    rw [jointGLen,ite_eq_right h9] at hj
    rw [jointGByte,ite_eq_right h9]
    exact pt.digits j hj

/-- Recode both public scalars while retaining the first digit buffer. -/
theorem jointPrep_ok (c : Joint.Cfg) {s : State} {base : Addr} {size u v : Nat}
    (hs : Scr s base size) (hu : u+32≤size) (hu8 : u%8=0)
    (hv : v+32≤size) (hv8 : v%8=0)
    (hg : c.gBits<4096) (hg8 : c.gBits%8=0) (hgb : c.gBits+jointGSpan c≤size)
    (hq : c.K.bits<4096) (hq8 : c.K.bits%8=0) (hqb : c.K.bits+264≤size)
    (hsep : c.gBits+jointGSpan c≤c.K.bits ∨ c.K.bits+264≤c.gBits)
    (hvs : v+32≤c.gBits ∨ c.gBits+jointGSpan c≤v) :
    WP isa (.seq (Joint.gPrep c u) (Impl.Weierstrass.AArch64.FastNaf.prep c.K v 5)) s fun t =>
      Scr t base size ∧
      (∀ j<jointGLen c,t.mem (off base (c.gBits+j))=jointGByte c (wordsVal s.mem base u 4) j) ∧
      (∀ j<257,t.mem (off base (c.K.bits+j))=FastNaf.byte 5 (wordsVal s.mem base v 4) j) ∧
      KeepRegs nafPrepClob s t ∧ Unch base [(c.gBits,jointGSpan c),(c.K.bits,264)] s.mem t.mem := by
  have hll := jointGLen_le_span c
  refine WP.seq (WP.mono (jointGPrep_ok c hs hu hu8 hg hg8 hgb)
    fun a ⟨sa,pa,ka,oa⟩ => ?_)
  have va : wordsVal a.mem base v 4=wordsVal s.mem base v 4 :=
    oa.wordsVal hvs (by have := hs.nowrap; omega)
  refine WP.mono (fastPrep_ok c.K (Or.inl rfl) sa hv hv8 hq hq8 hqb)
    fun t ⟨pt,kt,ot⟩ => ?_
  refine ⟨pt.scr,?_,?_,ka.trans kt,?_⟩
  · intro j hj
    rw [ot.unch.byte (by
      intro w hw; rw [List.mem_singleton.mp hw]; dsimp only; omega)
      (by have := hs.nowrap; omega)]
    exact pa j hj
  · rw [va] at pt
    exact pt.digits
  · exact oa.unch.trans ot.unch

end VG.Proof.Weierstrass.AArch64
