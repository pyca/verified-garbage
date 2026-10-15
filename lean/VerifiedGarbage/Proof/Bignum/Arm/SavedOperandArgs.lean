module

public import VerifiedGarbage.Impl.Bignum.Arm.SavedOperand
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandState
public import VerifiedGarbage.Proof.Bignum.Arm.StackPair
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Restore a private operand's pointer and length from the call frame -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem savedOperandArgs_ok (s : State) {base src : BitVec 32} {len k ps cs : Nat} {bs : List Byte}
    (h : SavedOperand base src len k ps cs bs s) :
    WP isa (.block (savedOperandArgs ps cs)) s fun t => t.gpr .r4 = src ∧ t.gpr .r6 = BitVec.ofNat 32 k ∧
      t.mem = s.mem ∧ Rest [.r4, .r6] s t := by
  have nowrap := h.nowrap
  have pfit := h.pointerFit
  have cfit := h.countFit
  refine WP.mono (stackPair_ok s .r4 .r6 ps cs (by decide) (by omega) (by omega)
    (by omega) (by omega) h.readable.1
    h.readable.2) ?_
  rintro t ⟨pointer, count, mem, rest⟩
  exact ⟨pointer.trans h.pointer, count.trans h.count, mem, rest⟩

end VG.Proof.Bignum.Arm
