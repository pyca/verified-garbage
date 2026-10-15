module

public import VerifiedGarbage.Proof.Bignum.Arm.WideProductHead
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
meta import VerifiedGarbage.Impl.Bignum.Arm.WideProduct
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Loading a secret product scalar leaks only its public source address -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

structure WideProductArgsInput (base ap : BitVec 32) (size : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  ptr : s.gpr .r0 = base
  source : s.mem.readW (off (State.addr base) 128) 32 = ap

theorem wideProductArgs_ct {base ap : BitVec 32} {size : Nat} (fit : 148 ≤ size) :
    RelCT isa (fun s t => WideProductArgsInput base ap size s ∧ WideProductArgsInput base ap size t)
      (.block wideProductArgs) (fun _ _ => True) := by
  let P := fun (s t : State) => WideProductArgsInput base ap size s ∧ WideProductArgsInput base ap size t
  have head : RelCT isa P (.block wideProductArgsHead) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have ready := head.wp (fun s t h => ⟨wideProductHead_ok s h.1.workspace fit h.1.ptr h.1.source,
    wideProductHead_ok t h.2.workspace fit h.2.ptr h.2.source⟩)
  have tail : RelCT isa (fun s t => True ∧ (s.gpr .r0 = base ∧ s.gpr .r1 = ap) ∧
      (t.gpr .r0 = base ∧ t.gpr .r1 = ap)) (.block wideProductArgsTail) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1.1.trans h.2.2.1.symm
    · exact h.2.1.2.trans h.2.2.2.symm
  exact RelCT.block_append (ready.seq tail)

end VG.Proof.Bignum.Arm
