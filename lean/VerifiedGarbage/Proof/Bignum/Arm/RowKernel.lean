module

public import VerifiedGarbage.Proof.Bignum.Arm.RowState
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.RowLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Impl.Bignum.Arm.Row
public import VerifiedGarbage.Impl.Bignum.Arm.RowCarry

/-! Runtime-width scalar multiply-add implementations share one arithmetic contract. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

/-- The same three public controls as the existing row_ct theorem. -/
def RowPublic (s t : State) : Prop :=
  s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12 ∧ s.gpr .lr = t.gpr .lr

/-- Runtime-width scalar multiply-add, with the existing arithmetic contract.
The fullCT field retains the existing unconditional rowFull_ct interface
without requiring downstream proofs to recover output pointer agreement. -/
structure RowKernel where
  code : Prog isa
  correct : ∀ (s : State) {base : BitVec 32} {size o b n : Nat},
    RowCtx s base size o b n → 0 < n →
    s.gpr .r0 = base + BitVec.ofNat 32 o →
    s.gpr .r12 = base + BitVec.ofNat 32 b →
    s.gpr .lr = BitVec.ofNat 32 n →
    WP isa code s (RowInv s base o b n n)
  ct : ConstantTime isa (fun _ => True) RowPublic code
  fullCT : ConstantTime isa (fun _ => True) RowPublic (.seq code rowCarry)
  stackZero : FrameStack.armStack code = 0
  callsNil : code.calls = []

/-- Existing code and contracts are the default; this emits no second body. -/
def RowKernel.baseline : RowKernel where
  code := row
  correct := by
    intro s base size o b n ctx hn hp0 hp12 hc
    exact row_ok s ctx hn hp0 hp12 hc
  ct := by exact row_ct
  fullCT := by exact rowFull_ct
  stackZero := rfl
  callsNil := rfl

end VG.Proof.Bignum.Arm
