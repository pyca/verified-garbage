module
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Segment
public import VerifiedGarbage.Proof.Sha3.AArch64.Sums


/-! # Resume rejection from the saved accepted prefix -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

/-- The entry of a resumed stream, its buffer at `x20`. -/
def continueEntry : List Instr :=
 [Impl.MlKem.AArch64.mov .x2 .x20,.movz .x .x5 56 0,.movz .x .x9 3329 0,.movz .x .x10 15 0]

theorem continueEntry_ok {w16 : Bool} (s : State)
    {B : Nat → Byte} {L : List Zq} {aP : Addr}
    (hp : Rej8.EnvW w16 56 B (s.gpr .x20) aP s) (hc : Rej8.Constants s)
    (hl : L.length≤256) (hcoeff : Rej8.Scalar.CoeffsW w16 s.mem aP L)
    (h3 : s.gpr .x3=cAddr w16 aP L.length) (h4 : (s.gpr .x4).toNat=256-L.length) :
    WP isa (.block (continueEntry)) s fun u => Only [.x2,.x5,.x9,.x10] s u ∧
      Rej8.EntryW w16 L 56 B (s.gpr .x20) aP u := by
  have hw : WP isa (.block (continueEntry)) s fun u =>
      Only [.x2,.x5,.x9,.x10] s u ∧ u.gpr .x2=s.gpr .x20 ∧
      (u.gpr .x5).toNat=56 ∧ (u.gpr .x9).toNat=q ∧ (u.gpr .x10).toNat=15 := by
    refine wp_mov fun a ha ea => wp_movz fun b hb eb => wp_movz fun c hc ec =>
      wp_movz fun u hu eu => wp_nil ?_
    refine ⟨(((ha.trans hb).trans hc).trans hu).mono (by decide),?_,?_,?_,?_⟩
    · rw [hu.get .x2,hc.get .x2,hb.get .x2,ea]
    · rw [hu.get .x5,hc.get .x5,eb]; rfl
    · rw [hu.get .x9,ec]; rfl
    · rw [eu]; rfl
  refine WP.mono (WP.keepV (by rfl) hw) fun u ⟨⟨hk,x2,x5,x9,x10⟩,hv⟩ => ⟨hk,?_⟩
  refine ⟨hp.transfer hk.mem hk.rd hk.wr (hk.get .x16),?_,hl,?_,x2,?_,?_,x5,x9,x10⟩
  · exact ⟨by rw [hv]; exact hc.index,by rw [hv]; exact hc.mask,
      by simpa only [hv] using hc.q,by simpa only [hv] using hc.weights,
      by simpa only [hv] using hc.zero⟩
  · rw [hk.mem]; exact hcoeff
  · rw [hk.get .x3,h3]
  · rw [hk.get .x4,h4]

theorem continue_ok {w16 : Bool} (s : State)
    {B : Nat → Byte} {L : List Zq} {aP : Addr}
    (hp : Rej8.EnvW w16 56 B (s.gpr .x20) aP s) (hc : Rej8.Constants s)
    (hl : L.length≤256) (hcoeff : Rej8.Scalar.CoeffsW w16 s.mem aP L)
    (h3 : s.gpr .x3=cAddr w16 aP L.length) (h4 : (s.gpr .x4).toNat=256-L.length) :
    WP isa (.seq (.block (continueEntry)) (Impl.MlKem.AArch64.Rej8.rejLoop w16)) s fun u =>
      Keep [.x0,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15] s u ∧
      Frame [polyRegion aP] s.mem u.mem ∧
      Rej8.Scalar.CoeffsW w16 u.mem aP (sampleAfter L B 56) ∧
      u.gpr .x3=cAddr w16 aP (sampleAfter L B 56).length ∧
      (u.gpr .x4).toNat=256-(sampleAfter L B 56).length ∧
      (u.gpr .x0).toNat=if (sampleAfter L B 56).length=256 then 1 else 0 := by
  refine WP.seq (WP.mono (continueEntry_ok s hp hc hl hcoeff h3 h4) fun a ⟨ha,he⟩ => ?_)
  refine WP.mono (Rej8.segment_ok he (by decide) (by decide)) fun u hu => ?_
  exact ⟨(ha.keep.trans hu.keep).mono (by decide),by rw [←ha.mem]; exact hu.acc.frame,
    hu.acc.coeffs,hu.acc.x3,hu.acc.x4,hu.status⟩

end VG.Proof.MlKem.AArch64.Paired
