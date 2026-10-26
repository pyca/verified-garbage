module
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify

import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! # Fixed-length masked signature output -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.WriteBytes (writeW8_apply)

abbrev copyMaskedByte := VG.Impl.Dsa.AArch64.SignVerify.copyMaskedByte

theorem masked_byte (b : Byte) (valid : Bool) :
    (b.zeroExtend 64 &&& mask valid).setWidth 8 = if valid then b else 0 := by
  cases valid <;> simp [mask, BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le]
  exact BitVec.and_allOnes

structure CopyMaskedInv (s : State) (src out : Addr) (n j : Nat) (valid : Bool) (t : State) : Prop where
  keep : Keep [.x3, .x1, .x2, .x9] s t
  rsi : t.gpr .x1 = src + BitVec.ofNat 64 j
  rdx : t.gpr .x2 = out + BitVec.ofNat 64 j
  rcx : t.gpr .x9 = BitVec.ofNat 64 (n - j)
  bytes : ∀ i < j, t.mem (out + BitVec.ofNat 64 i) = if valid then s.mem (src + BitVec.ofNat 64 i) else 0
  frame : ∀ x, (∀ i < j, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem copyMasked_ok {s : State} {src out : Addr} {n : Nat} {valid : Bool}
    (hsi : s.gpr .x1 = src) (hdx : s.gpr .x2 = out) (hcx : s.gpr .x9 = BitVec.ofNat 64 n)
    (h8 : s.gpr .x8 = mask valid) (h1 : 0 < n) (h64 : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j) :
    WP isa (.loop (.block copyMaskedByte) (.nonzero .x .x9)) s fun t =>
      (∀ i < n, t.mem (out + BitVec.ofNat 64 i) = if valid then s.mem (src + BitVec.ofNat 64 i) else 0) ∧
      (∀ x, (∀ i < n, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.x3, .x1, .x2, .x9] s t := by
  refine WP.mono (wp_countdown (N := n) h64 h1 (fun j t => CopyMaskedInv s src out n j valid t)
    ?_ ⟨Keep.refl _ _, by simpa using hsi, by simpa using hdx, by simpa using hcx,
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩ hcx)
    fun t ht => ⟨ht.bytes, ht.frame, ht.keep⟩
  intro j hj t ht hcount
  have hrd : InRegions (t.rd ++ t.wr) (src + BitVec.ofNat 64 j) 1 := by
    rw [ht.keep.rd, ht.keep.wr]; exact hr j hj
  have hwr : InRegions t.wr (out + BitVec.ofNat 64 j) 1 := by
    rw [ht.keep.wr]; exact hw j hj
  have ht8 := (ht.keep.gpr .x8 (by decide)).trans h8
  have hval := ht.frame (src + BitVec.ofNat 64 j) (fun i hi => hsep j hj i (by omega))
  refine WP.mono (WP.keep [.x3, .x1, .x2, .x9] (Q := fun u =>
    u.mem = t.mem.writeW (out + BitVec.ofNat 64 j) (if valid then s.mem (src + BitVec.ofNat 64 j) else (0 : Byte)) ∧
    u.gpr .x1 = src + BitVec.ofNat 64 (j + 1) ∧ u.gpr .x2 = out + BitVec.ofNat 64 (j + 1) ∧
    u.gpr .x9 = BitVec.ofNat 64 (n - (j + 1))) ?_ rfl rfl rfl)
    fun u ⟨⟨hum, husi, hudx, hucx⟩, hku⟩ => ?_
  · unfold copyMaskedByte VG.Impl.Dsa.AArch64.SignVerify.copyMaskedByte
    have hb : ((s.mem (src + BitVec.ofNat 64 j)).setWidth 32).setWidth 64 =
        (s.mem (src + BitVec.ofNat 64 j)).zeroExtend 64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.zeroExtend]
      have := (s.mem (src + BitVec.ofNat 64 j)).isLt
      omega
    have hp : BitVec.ofNat 64 (n - j) - (1#64) = BitVec.ofNat 64 (n - (j + 1)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    brun [ht.rsi, ht.rdx, ht.rcx, ht8, hrd, hwr, read_one, hb, hval, masked_byte,
      hp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rfl
  · refine ⟨⟨(ht.keep.trans hku).mono (by decide), husi, hudx, hucx, ?_, ?_⟩, ?_⟩
    · intro i hi
      rw [hum, writeW8_apply]
      by_cases hij : i = j
      · subst i; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
        exact ht.bytes i (by omega)
    · intro x hx
      rw [hum, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
      exact ht.frame x fun i hi => hx i (by omega)

    · rw [hucx, hcount]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega

end VG.Proof.Dsa.AArch64
