module
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Probe
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Scalar
import VerifiedGarbage.Proof.Rc4.AArch64.Vec


/-! # The public rejection-count branch selects a proved vector or scalar step -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def choosePrefix : List Instr := [.subImm .x .x6 .x4 8,.lsr .x .x6 .x6 63]

theorem choosePrefix_ok {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ s : State} (h : Scalar.InvW w16 initial N B bP aP s₀ t s) (hc : Constants s) :
    WP isa (.block choosePrefix) s fun u =>
      Scalar.InvW w16 initial N B bP aP s₀ t u ∧ Constants u ∧
        ((u.gpr .x6 == 0)=true ↔ 8≤(u.gpr .x4).toNat) := by
  have hw : WP isa (.block choosePrefix) s fun u =>
      Scalar.InvW w16 initial N B bP aP s₀ t u ∧
        ((u.gpr .x6 == 0)=true ↔ 8≤(u.gpr .x4).toNat) := by
    refine wp_subImm (by decide) fun a ha ea => wp_lsr (by decide) fun u hu eu => wp_nil ?_
    have hk := (ha.keep.trans hu.keep).mono (rs' := [.x6]) (by decide)
    have hm : u.mem=s.mem := hu.mem.trans ha.mem
    refine ⟨⟨Scalar.acc_keep h.acc hk hm,(h.keep.trans hk).mono (by decide),
      by rw [hk.get .x2,h.x2],by rw [hk.get .x5,h.x5],by rw [hk.get .x10,h.x10]⟩,?_⟩
    rw [eu,ea,hu.gpr .x4 (by decide),ha.gpr .x4 (by decide),beq_iff_eq]
    have hb : (s.gpr .x4).toNat≤256 := by rw [h.acc.x4]; omega
    bv_omega
  refine WP.mono (WP.keepV (by decide) hw) fun u ⟨⟨hi,he⟩,hv⟩ => ⟨hi,?_,he⟩
  exact ⟨by rw [hv]; exact hc.index,by rw [hv]; exact hc.mask,
    by simpa only [hv] using hc.q,by simpa only [hv] using hc.weights,
    by simpa only [hv] using hc.zero⟩

end VG.Proof.MlKem.AArch64.Rej8
