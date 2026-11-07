module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.Inv
public import VerifiedGarbage.Proof.Divstep.WordDef
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.Divstep.WordBasic
import VerifiedGarbage.Proof.Mont.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-!
# Inversion by divsteps on AArch64: the word divstep

Facts of 64-bit words for the divstep on words: the top bit (`msb_word`)
and adding all ones and one (`add_not0_one`, `toInt_not0`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Divstep (WSt wstep)

theorem one64 : BitVec.ofNat 64 1 = (1 : BitVec 64) := rfl
theorem msb_word (x : BitVec 64) : x >>> 63 = if x.msb then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  have := x.isLt
  by_cases h : 2 ^ 63 ≤ x.toNat
  · simp only [show 2 ^ (64 - 1) ≤ x.toNat by simpa using h, decide_true, ↓reduceIte]
    show x.toNat / 2 ^ 63 = 1
    omega
  · simp only [show ¬ 2 ^ (64 - 1) ≤ x.toNat by simpa using h, decide_false, Bool.false_eq_true, ↓reduceIte]
    show x.toNat / 2 ^ 63 = 0
    omega

theorem add_not0_one (x : BitVec 64) : x + ~~~(BitVec.ofNat 64 0) + BitVec.ofNat 64 1 = x := by
  rw [BitVec.add_assoc, show ~~~(BitVec.ofNat 64 0) + BitVec.ofNat 64 1 = 0 from by decide]; simp

theorem add_not0_one' (x : BitVec 64) : x + ~~~(0#64) + 1 = x := add_not0_one x

theorem int_m1p1 (a : Int) : a + -1 + 1 = a := by omega

theorem toInt_not0 : (~~~(BitVec.ofNat 64 0)).toInt = -1 := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_not, BitVec.toNat_ofNat]
  simp only [Nat.zero_mod, Nat.sub_zero]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  omega

end VG.Proof.Weierstrass.AArch64
