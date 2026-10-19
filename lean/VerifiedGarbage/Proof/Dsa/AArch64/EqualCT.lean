module
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.Operands
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks

import VerifiedGarbage.Proof.Dsa.AArch64.EqualHead
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Dsa.AArch64.Operands
meta import VerifiedGarbage.Impl.Dsa.AArch64.Checks
meta import VerifiedGarbage.Proof.Dsa.AArch64.EqualHead
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant-time equality of DSA byte buffers -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure EqualPublic where
  base : Addr
  left : Addr
  right : Addr
  length : Nat

def EqualPre (a b : Operand) (p : EqualPublic) (s : State) : Prop :=
  ∃ Z, Scr s p.base Z ∧ pWorkspace ≤ Z ∧ s.gpr .x0 = p.base ∧
    pointerValue s.mem p.base a.pointer = p.left ∧ pointerValue s.mem p.base b.pointer = p.right ∧
    word s.mem p.base a.length.offset = BitVec.ofNat 64 p.length

def EqualRegs (p : EqualPublic) (s : State) : Prop :=
  s.gpr .x0 = p.base ∧ s.gpr .x1 = p.left ∧ s.gpr .x2 = p.right ∧
    s.gpr .x9 = BitVec.ofNat 64 p.length

/-- The equality check and mask accumulation depend only on the public
workspace address, operand pointers and length. Input contents remain secret. -/
theorem equal_ct {a b : Operand} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (unequal : Bool) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (Core.pointer a.pointer ++
      ([mov .x1 .x3] : List Instr) ++ Core.pointer b.pointer ++
      ([mov .x2 .x3, Core.field .x9 a.length,
        movi .x8 0] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (EqualPre a b)) (Checks.equal a b unequal) (fun _ _ => True) := by
  unfold Checks.equal seqs
  refine RelCT.seq (two_piece (Ψ := EqualRegs) [.x0]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr
      obtain ⟨_, _, _, hdi, _⟩ := h
      simp only [List.mem_singleton] at hr
      subst r
      exact hdi)) hT ?_) ?_
  · intro p s ⟨Z, hs, hZ, hdi, hleft, hright, hlen⟩
    exact WP.mono (equalHead_ok hs hdi hZ a b ha hb) fun t h =>
      ⟨(h.2.2.2.2.2.gpr .x0 (by decide)).trans hdi, h.1.trans hleft,
        h.2.1.trans hright, h.2.2.1.trans hlen⟩
  have hp : Pins EqualRegs [.x0, .x1, .x2, .x9] :=
    pins_of (fun p r => if r = .x0 then p.base else if r = .x1 then p.left
      else if r = .x2 then p.right else BitVec.ofNat 64 p.length) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2)
  cases unequal <;> exact two_taint [.x0, .x1, .x2, .x9] hp (by taint_decide)

end VG.Proof.Dsa.AArch64
