module
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify

import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
public import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.X86_64.Operands
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import Mathlib.Tactic.ToAdditive
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant-time clearing of a rejected DSA signature -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure FailurePublic where
  base : Addr
  output : Addr
  width : Nat

def FailurePre (p : FailurePublic) (s : State) : Prop :=
  ∃ Z, Scr s p.base Z ∧ pWorkspace ≤ Z ∧ s.gpr .rdi = p.base ∧
    word s.mem p.base Field.out.offset = p.output ∧
    word s.mem p.base Field.qLen.offset = BitVec.ofNat 64 p.width

def FailureRegs (p : FailurePublic) (s : State) : Prop :=
  s.gpr .rdi = p.base ∧ s.gpr .rsi = p.output ∧ s.gpr .rcx = BitVec.ofNat 64 (2 * p.width)

theorem signFailure_ct : RelCT isa (Two FailurePre) SignVerify.signFailure (fun _ _ => True) := by
  unfold SignVerify.signFailure seqs
  refine RelCT.seq (two_piece (Ψ := FailureRegs) [.rdi]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr
      obtain ⟨_, _, _, hdi, _⟩ := h
      simp only [List.mem_singleton] at hr
      subst r
      exact hdi)) (by taint_decide) ?_) ?_
  · intro p s ⟨Z, hs, hZ, hdi, ho, hq⟩
    refine WP.mono (WP.keep [.rax, .rsi, .rcx] (Q := fun t =>
      t.gpr .rsi = p.output ∧ t.gpr .rcx = BitVec.ofNat 64 (2 * p.width)) ?_ rfl)
      fun t ⟨⟨hsi, hcx⟩, hk⟩ => ⟨(hk.gpr (by decide)).trans hdi, hsi, hcx⟩
    xrun [State.ea, Core.field, fieldAddress, hdi, ho, hq,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ)]
    rw [BitVec.ofNat_add_ofNat, Nat.two_mul]
  · exact two_taint [.rdi, .rsi, .rcx]
      (pins_of (fun p r => if r = .rdi then p.base else if r = .rsi then p.output else BitVec.ofNat 64 (2 * p.width))
        (by
          intro p s h r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2)) (by taint_decide)

end VG.Proof.Dsa.X86_64
