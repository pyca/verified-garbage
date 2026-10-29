module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Tail
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Vector
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Probe
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Scalar

import VerifiedGarbage.Proof.Rc4.AArch64.Vec
/-! # One mixed vector/scalar rejection iteration, including early success -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Rej8Choice.lean`, which only this module imported.
section

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
end

end

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def body (w16 : Bool := false) : Prog isa := .seq (.block choosePrefix)
  (.ite (.zero .x .x6) (.block (Impl.MlKem.AArch64.Rej8.rejEight w16))
    (.seq (scalarFour w16) (.ite (.zero .x .x4) (.block [.movz .x .x5 0 0]) (.block []))))

structure ResultW (w16 : Bool) (initial : List Zq) (N : Nat) (B : Nat → Byte) (aP : Addr) (s₀ u : State) :
    Prop where
  acc : Scalar.AccW w16 aP s₀ (Scalar.LA initial B N) u
  keep : Keep Scalar.lRegs s₀ u
  constants : Constants u

abbrev Result := ResultW false

private theorem constants_of_vec {s u : State} (h : Constants s) (hv : u.v=s.v) : Constants u :=
  ⟨by rw [hv]; exact h.index,by rw [hv]; exact h.mask,
   by simpa only [hv] using h.q,by simpa only [hv] using h.weights,by simpa only [hv] using h.zero⟩

theorem body_ok {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ s : State} (hp : EnvW w16 N B bP aP s₀) (h : Scalar.InvW w16 initial N B bP aP s₀ t s)
    (hc : Constants s) (ht : t+4≤N) :
    WP isa (body w16) s fun u =>
      (Scalar.InvW w16 initial N B bP aP s₀ (t+4) u ∧ Constants u) ∨
        (ResultW w16 initial N B aP s₀ u ∧ u.gpr .x5=0) := by
  refine WP.seq (WP.mono (choosePrefix_ok h hc) fun a ⟨ha,hac,he⟩ => ?_)
  refine WP.ite (a.gpr .x6 == 0) (eval_zero _ _) (fun hz => ?_) (fun _ => ?_)
  · exact WP.mono (vector_ok hp ha hac ht (he.mp hz)) fun _ hv => Or.inl hv
  · refine WP.seq (WP.mono (scalarFour_ok hp.toLPreW ha ht) fun b ⟨hb,hv⟩ => ?_)
    have hbc := constants_of_vec hac hv
    refine WP.ite (b.gpr .x4 == 0) (eval_zero _ _) (fun hz => ?_) (fun _ => ?_)
    · have hfull : (Scalar.LA initial B (t+4)).length=n := by
        rw [eq_zero_iff,decide_eq_true_eq,hb.acc.x4] at hz
        have := hb.acc.len
        change _=256
        omega
      have heq := sampleAfter_full hfull N ht
      have hw : WP isa (.block [.movz .x .x5 0 0]) b fun u =>
          Scalar.AccW w16 aP s₀ (Scalar.LA initial B N) u ∧
          Keep Scalar.lRegs s₀ u ∧ u.gpr .x5=0 := by
        refine wp_movz fun u hu eu => wp_nil ?_
        refine ⟨?_,(hb.keep.trans hu.keep).mono (by decide),eu⟩
        rw [show Scalar.LA initial B N=Scalar.LA initial B (t+4) from heq]
        exact Scalar.acc_keep hb.acc hu.keep hu.mem
      exact WP.mono (WP.keepV (by decide) hw) fun _ ⟨⟨ac,ke,x5⟩,ve⟩ =>
        Or.inr ⟨⟨ac,ke,constants_of_vec hbc ve⟩,x5⟩
    · exact wp_nil (Or.inl ⟨hb,hbc⟩)

end VG.Proof.MlKem.AArch64.Rej8
