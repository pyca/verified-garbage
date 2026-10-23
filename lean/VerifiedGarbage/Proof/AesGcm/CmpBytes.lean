module

public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.AesGcm.Bytes

/-!
# AES-GCM: comparing padded tags a doubleword at a time

Untrusted: everything here is checked by Lean, and nothing depends on a
target. Two 16-byte blocks are equal iff the OR of the XORs of their
doublewords is 0 (`words_eq`); a tag of `t` bytes written over 16 zero
bytes reads back padded (`pad_bytes`), and two tags so padded are equal iff
they are (`pad_eq`); `(d ||| -d) >>> 63` is 0 iff `d` is (`neg_or_msb`), as
an implementation tests a word without a branch.
-/

@[expose] public section

namespace VG.Proof.AesGcm

open VG VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)
open VG.Proof.Cmac (le8)

theorem le8_inj {a b : BitVec 64} (h : le8 a = le8 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (fun l => (l.getD (i / 8) 0).getLsbD (i % 8)) h
  simp only [Proof.Cmac.getD_le8 _ (show i / 8 < 8 by omega), BitVec.getLsbD_extractLsb',
    show i % 8 < 8 by omega, decide_true, Bool.true_and, show 8 * (i / 8) + i % 8 = i by omega] at e
  exact e

/-- Two blocks are equal iff their doublewords are. -/
theorem words_eq (m : Mem) (p q : Addr) :
    ((m.readW p 64 ^^^ m.readW q 64) ||| (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64)
      = 0) ↔ bytesAt m p 16 = bytesAt m q 16 := by
  rw [Proof.Cmac.bytesAt_split m p, Proof.Cmac.bytesAt_split m q, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW]
  constructor
  · intro h
    have h₁ : m.readW p 64 ^^^ m.readW q 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or] at this ⊢
      simp_all
    have h₂ : m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or] at this ⊢
      simp_all
    rw [BitVec.xor_eq_zero_iff.mp h₁, BitVec.xor_eq_zero_iff.mp h₂]
  · intro h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [Proof.Cmac.length_le8, Proof.Cmac.length_le8])
    rw [le8_inj h₁, le8_inj h₂, BitVec.xor_self, BitVec.xor_self, BitVec.or_self]; rfl

/-- `xs` written over 16 zero bytes at `P`. -/
theorem pad_bytes {m : Mem} {P : Addr} (hz : bytesAt m P 16 = zeros 16) (xs : List Byte) (hx : xs.length ≤ 16) :
    bytesAt (writeBytes m P xs) P 16 = xs ++ zeros (16 - xs.length) := by
  rw [bytesAt_writeBytes_prefix _ _ _ hx (by decide)]
  congr 1
  rw [show (16 : Nat) = xs.length + (16 - xs.length) by omega, bytesAt_add] at hz
  have e := congrArg (List.drop xs.length) hz
  rw [List.drop_left' (length_bytesAt _ _ _)] at e
  rw [e, show xs.length + (16 - xs.length) = 16 by omega, zeros, List.drop_replicate]
  rfl

/-- Tags of the same length padded alike are equal iff they are. -/
theorem pad_eq {xs ys : List Byte} {k : Nat} (h : xs.length = ys.length) :
    xs ++ zeros k = ys ++ zeros k ↔ xs = ys :=
  ⟨fun e => (List.append_inj e h).1, fun e => by rw [e]⟩

/-- The top bit of `d ||| -d`: whether `d` is not 0. -/
theorem neg_or_msb (d : BitVec 64) :
    (d ||| (0 - d)) >>> 63 = if d = 0 then 0 else 1 := by
  by_cases h : d = 0
  · subst h; decide
  · simp only [h, ite_false]
    apply BitVec.eq_of_toNat_eq
    have hd : d.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    have hn : (0 - d).toNat = 2 ^ 64 - d.toNat := by
      rw [BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl]; have := d.isLt; omega
    have hl : (d ||| (0 - d)).toNat < 2 ^ 64 := (d ||| (0 - d)).isLt
    have h₁ : d.toNat ≤ (d ||| (0 - d)).toNat := by rw [BitVec.toNat_or]; exact Nat.left_le_or
    have h₂ : (0 - d).toNat ≤ (d ||| (0 - d)).toNat := by rw [BitVec.toNat_or]; exact Nat.right_le_or
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    show _ = 1
    have := d.isLt
    omega

end VG.Proof.AesGcm
