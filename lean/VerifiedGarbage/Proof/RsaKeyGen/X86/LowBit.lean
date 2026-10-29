module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowBit
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Subtract
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Words
/-! # Native subtraction and masking isolate the paired word's lowest set bit -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/NegPair.lean`, which only this module imported.
section

/-! # Native subtraction through the borrow forms the negation of a 64-bit pair -/

section
namespace VG.Proof.RsaKeyGen.X86.LowBit
open VG VG.Proof.Mont.X86

theorem neg_pair (lo hi : BitVec 32) :
    (0#32 - hi - (BitVec.ofBool (decide (0 < lo.toNat))).setWidth 32) ++ (0#32 - lo) = -(hi ++ lo) := by
  let borrow := decide (0 < lo.toNat)
  let carry := decide (0 < hi.toNat + borrow.toNat)
  have L := Mod64.sub_rel (0#32) lo
  have H := sbb_rel (0#32) hi borrow
  simp only [BitVec.toNat_zero, Nat.zero_add] at L H
  change (0#32 - lo).toNat + lo.toNat = 2 ^ 32 * borrow.toNat at L
  change (0#32 - hi - (BitVec.ofBool borrow).setWidth 32).toNat + hi.toNat + borrow.toNat =
    2 ^ 32 * carry.toNat at H
  have paired : ((0#32 - hi - (BitVec.ofBool borrow).setWidth 32) ++ (0#32 - lo)).toNat +
      (hi ++ lo).toNat = 2 ^ 64 * carry.toNat := by
    rw [Gcd64.append_pair, Gcd64.append_pair]
    unfold Mod64.pair
    omega
  have outputBound := ((0#32 - hi - (BitVec.ofBool borrow).setWidth 32) ++ (0#32 - lo)).isLt
  have inputBound := (hi ++ lo).isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_neg]
  change ((0#32 - hi - (BitVec.ofBool borrow).setWidth 32) ++ (0#32 - lo)).toNat = _
  cases C : carry <;> rw [C] at paired <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one] at paired <;> omega

end VG.Proof.RsaKeyGen.X86.LowBit
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowBit
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.LowBit

theorem code_ok (s : State) :
    WP isa (.block code) s fun t =>
      t.gpr .edx ++ t.gpr .eax = (s.gpr .esi ++ s.gpr .ebx) &&& -(s.gpr .esi ++ s.gpr .ebx) ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx] s t := by
  unfold code
  refine wp_movS rfl fun a A _ => wp_subS rfl fun b B cfB => wp_movS rfl fun c C cfC => ?_
  refine wp_sbbS rfl (cfC.trans cfB) fun d D _ => wp_and fun e E => wp_and fun t T => WP.block_nil ?_
  have low : t.gpr .eax = (0#32 - s.gpr .ebx) &&& s.gpr .ebx := by
    rw [T.other .eax (by decide), E.gpr, D.other .eax (by decide), C.other .eax (by decide),
      B.gpr, A.gpr, A.other .ebx (by decide), D.other .ebx (by decide), C.other .ebx (by decide),
      B.other .ebx (by decide), A.other .ebx (by decide)]
    rfl
  have high : t.gpr .edx = (0#32 - s.gpr .esi - (BitVec.ofBool (decide (0 < (s.gpr .ebx).toNat))).setWidth 32)
      &&& s.gpr .esi := by
    rw [T.gpr, E.other .edx (by decide), D.gpr, C.gpr, C.other .esi (by decide), B.other .esi (by decide),
      A.other .esi (by decide), A.gpr, A.other .ebx (by decide),
      E.other .esi (by decide), D.other .esi (by decide), C.other .esi (by decide), B.other .esi (by decide),
      A.other .esi (by decide)]
    rfl
  refine ⟨?_, ?_, (((((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).widen E.keeps).widen T.keeps⟩
  · rw [low, high, ← BitVec.and_append, neg_pair, BitVec.and_comm]
  · rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.LowBit
