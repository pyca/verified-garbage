module

import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Core
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# A candidate on AArch64: Miller–Rabin's comparisons

`eqMask_ok`: the mask of `[aY] = [j]`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

/-- `eqMask j`: `x15 :=` the mask of `[aY] = [j]`. -/
theorem eqMask_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) :
    WP isa (seqs (eqMask j)) s fun t =>
      t.gpr .x15 = mask (decide (wv s.mem B (slot w aY) w = wv s.mem B (slot w j) w)) ∧ t.mem = s.mem ∧
      Keep mmRegs s t := by
  unfold eqMask
  refine wp_seqs_append (by simp [eqA]) (by simp) ?_
  refine WP.mono (eqA_ok h (a := aY) (b := j) (by decide) hj) fun s₁ ⟨hz, m₁, _, _, k₁⟩ => ?_
  have e : (!decide (2 ^ 64 ≤ (s₁.gpr .x9).toNat + (~~~(BitVec.setWidth 64 1#16 : BitVec 64)).toNat + 1)) =
      decide (wv s.mem B (slot w aY) w = wv s.mem B (slot w j) w) := (lt_one_flag _).trans (decide_eq_decide.mpr hz)
  simp only [seqs]
  refine WP.mono (WP.keep [.x3, .x4, .x7, .x15] (Q := fun t => t.gpr .x15 =
      mask (decide (wv s.mem B (slot w aY) w = wv s.mem B (slot w j) w)) ∧ t.mem = s₁.mem) (by
    brun [borrowMask, Bool.toNat_true, csel_mask', e]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h15, mt⟩, k⟩ => ⟨h15, mt.trans m₁, (k₁.trans k).mono (by decide)⟩


theorem neg_bit (b : Bool) : BitVec.setWidth 64 0#16 - BitVec.ofNat 64 b.toNat = mask b := by
  cases b <;> decide

theorem shl_one (x : BitVec 64) : x <<< 1 = x + x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_two]

theorem ofNat64_pred {n : Nat} (h : 1 ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1#64 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show n - 1 < 2 ^ 64 by omega)]
  omega

end VG.Proof.RsaKeyGen.AArch64
