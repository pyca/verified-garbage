module

public import VerifiedGarbage.Proof.Dsa.AArch64.Failure
meta import VerifiedGarbage.Proof.Dsa.AArch64.Failure
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Constant-time clearing of a rejected DSA signature -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure FailurePublic where
  base : Addr
  output : Addr
  width : Nat

def FailurePre (p : FailurePublic) (s : State) : Prop :=
  ∃ Z, Scr s p.base Z ∧ pWorkspace ≤ Z ∧ s.gpr .x0 = p.base ∧
    word s.mem p.base Field.out.offset = p.output ∧
    word s.mem p.base Field.qLen.offset = BitVec.ofNat 64 p.width

def FailureRegs (p : FailurePublic) (s : State) : Prop :=
  s.gpr .x0 = p.base ∧ s.gpr .x1 = p.output ∧ s.gpr .x9 = BitVec.ofNat 64 (2 * p.width)

theorem signFailure_ct : RelCT isa (Two FailurePre) SignVerify.signFailure (fun _ _ => True) := by
  unfold SignVerify.signFailure seqs
  refine RelCT.seq (two_piece (Ψ := FailureRegs) [.x0]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr
      obtain ⟨_, _, _, hdi, _⟩ := h
      simp only [List.mem_singleton] at hr
      subst r
      exact hdi)) (by taint_decide) ?_) ?_
  · intro p s ⟨Z, hs, hZ, hdi, ho, hq⟩
    refine WP.mono (WP.keep [.x1, .x9, .x3] (Q := fun t =>
      t.gpr .x1 = p.output ∧ t.gpr .x9 = BitVec.ofNat 64 (2 * p.width)) ?_ (by decide) (by decide)
        (by decide +kernel))
      fun t ⟨⟨h1, h9⟩, hk⟩ => ⟨(hk.gpr _ (by decide)).trans hdi, h1, h9⟩
    unfold Core.field
    brun [hdi, field_enc, ho, hq,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ)]
    rw [BitVec.ofNat_add_ofNat, Nat.two_mul]
  · exact two_taint [.x0, .x1, .x9]
      (pins_of (fun p r => if r = .x0 then p.base else if r = .x1 then p.output else BitVec.ofNat 64 (2 * p.width))
        (by
          intro p s h r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2)) (by taint_decide)

end VG.Proof.Dsa.AArch64
