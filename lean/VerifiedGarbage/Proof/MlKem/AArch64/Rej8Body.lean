module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Choice

/-! # One mixed vector/scalar rejection iteration, including early success -/

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
