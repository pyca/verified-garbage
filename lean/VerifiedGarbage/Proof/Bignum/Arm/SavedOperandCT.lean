module

public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperand
public import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Saved private operand imports reveal no source bytes -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem savedOperand_ct {base src : BitVec 32} {len w k ps cs o : Nat} {bs1 bs2 : List Byte} (ho : o < 8) :
    RelCT isa (fun s t => (ArithmeticReady base len w s ∧ SavedOperand base src len k ps cs bs1 s) ∧
      (ArithmeticReady base len w t ∧ SavedOperand base src len k ps cs bs2 t) ∧ s.sp = t.sp)
      (savedOperand o ps cs) (fun _ _ => True) := by
  let P := fun (s t : State) => (ArithmeticReady base len w s ∧ SavedOperand base src len k ps cs bs1 s) ∧
    (ArithmeticReady base len w t ∧ SavedOperand base src len k ps cs bs2 t) ∧ s.sp = t.sp
  let Q := fun s : State => ArithmeticReady base len w s ∧ s.gpr .r4 = src ∧ s.gpr .r6 = BitVec.ofNat 32 k
  have args : RelCT isa P (.block (savedOperandArgs ps cs)) (fun s t => s.sp = t.sp) :=
    (stackLoads_ct [(.r4, ps), (.r6, cs)]).mono (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (s : State) {bs : List Byte} (h : ArithmeticReady base len w s)
      (source : SavedOperand base src len k ps cs bs s) : WP isa (.block (savedOperandArgs ps cs)) s Q := by
    refine WP.mono (savedOperandArgs_ok s source) ?_
    rintro t ⟨ptr, count, mem, rest⟩
    exact ⟨h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr), ptr, count⟩
  have ready := args.wp (fun s t h => ⟨wp s h.1.1 h.1.2, wp t h.2.1.1 h.2.1.2⟩)
  exact ready.seq ((importOperand_ct ho).mono (fun _ _ h =>
    ⟨h.2.1.1, h.2.2.1, h.2.1.2.1, h.2.2.2.1, h.2.1.2.2, h.2.2.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
