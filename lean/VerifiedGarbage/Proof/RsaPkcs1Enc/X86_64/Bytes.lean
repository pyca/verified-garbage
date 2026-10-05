import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# RSAES-PKCS1-v1_5 on x86-64: bytes at offsets of a base

Byte `d` of a buffer at `base` is `byte m base d`. These lemmas read bytes
and words through writes of bytes and words at other offsets (`byte_wb`,
`byte_ww`, `word_wb`), for offsets that do not wrap around, and turn a
store of a byte into `Outside` (`writeB_outside`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.WriteBytes (writeW8_apply)

/-- A byte, zero-extended and truncated back. -/
theorem trunc_zext (b : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 b) = b :=
  BitVec.eq_of_toNat_eq (by simp)

theorem zext_toNat (b : Byte) : (BitVec.setWidth 64 b).toNat = b.toNat := by
  have := b.isLt; simp; omega

theorem zero_trunc : BitVec.setWidth 8 (BitVec.setWidth 64 (0 : BitVec 32)) = 0 := rfl

theorem one64_toNat : (1 : BitVec 64).toNat = 1 := rfl

/-- Byte `d` of the buffer at `base`. -/
abbrev byte (m : Mem) (base : Addr) (d : Nat) : Byte := m (off base d)

theorem ofs_off0 (base : Addr) {d : Nat} (h : d < 2 ^ 64) : ofs base (off base d) = d := by
  have := ofs_off base (d := d) (i := 0) (by omega)
  rwa [BitVec.add_zero, Nat.add_zero] at this

theorem byte_wb_self (m : Mem) (base : Addr) (d : Nat) (v : Byte) :
    byte (m.writeW (off base d) v) base d = v := by
  simp only [byte, writeW8_apply, ↓reduceIte]

/-- A byte past a store of a byte at another offset. -/
theorem byte_wb (m : Mem) (base : Addr) {d d' : Nat} (v : Byte) (h : d ≠ d') (hd : d < 2 ^ 64)
    (hd' : d' < 2 ^ 64) : byte (m.writeW (off base d') v) base d = byte m base d := by
  simp only [byte, writeW8_apply, off, Offset.add_ofNat_ne base hd hd' h, ↓reduceIte]

/-- A store of a byte changes only that byte. -/
theorem writeB_outside (m : Mem) (base : Addr) {d : Nat} (v : Byte) (h : d < 2 ^ 64) :
    Outside base d 1 m (m.writeW (off base d) v) := by
  intro x hx
  rw [writeW8_apply]
  have : x ≠ off base d := by
    rintro rfl
    rw [ofs_off0 base h] at hx
    omega
  simp only [this, ↓reduceIte]

/-- A byte past a store of a word elsewhere. -/
theorem byte_ww (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 64) (h : d + 1 ≤ d' ∨ d' + 8 ≤ d)
    (hd : d < 2 ^ 64) (hd' : d' + 8 ≤ 2 ^ 64) : byte (m.writeW (off base d') v) base d = byte m base d := by
  have := writeW_outside m base v hd'
  refine this _ ?_
  rw [ofs_off0 base hd]
  omega

/-- A word past a store of a byte elsewhere. -/
theorem word_wb (m : Mem) (base : Addr) {d d' : Nat} (v : Byte) (h : d + 8 ≤ d' ∨ d' + 1 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (hd' : d' < 2 ^ 64) : word (m.writeW (off base d') v) base d = word m base d :=
  (writeB_outside m base v hd').word (by omega) hd

/-- A word past a store of a word elsewhere. -/
theorem word_ww (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 64) (h : d + 8 ≤ d' ∨ d' + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (hd' : d' + 8 ≤ 2 ^ 64) : word (m.writeW (off base d') v) base d = word m base d :=
  (writeW_outside m base v hd').word (by omega) hd

/-- `Outside` past a store of a byte within its range. -/
theorem Outside.wb {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat} (v : Byte)
    (h₁ : o ≤ d) (h₂ : d < o + n) (hd : d < 2 ^ 64) : Outside base o n m (m'.writeW (off base d) v) :=
  fun x hx => ((writeB_outside m' base v hd) x (by omega)).trans (h x hx)

/-- `Outside` past a store of a word within its range. -/
theorem Outside.ww {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat} (v : BitVec 64)
    (h₁ : o ≤ d) (h₂ : d + 8 ≤ o + n) (hd : d + 8 ≤ 2 ^ 64) : Outside base o n m (m'.writeW (off base d) v) :=
  fun x hx => ((writeW_outside m' base v hd) x (by omega)).trans (h x hx)

/-! ### Stores at the base itself (offset 0, as `xrun` leaves them) -/

theorem off_zero (p : Addr) : off p 0 = p := BitVec.add_zero p

theorem word_ww0 (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64) :
    word (m.writeW base v) base d = word m base d := by
  have := word_ww m base v (d := d) (d' := 0) (.inr h) hd (by omega)
  rwa [off_zero] at this

theorem byte_ww0 (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : 8 ≤ d) (hd : d < 2 ^ 64) :
    byte (m.writeW base v) base d = byte m base d := by
  have := byte_ww m base v (d := d) (d' := 0) (.inr h) hd (by omega)
  rwa [off_zero] at this

theorem word0_ww (m : Mem) (base : Addr) {d' : Nat} (v : BitVec 64) (h : 8 ≤ d') (hd' : d' + 8 ≤ 2 ^ 64) :
    (m.writeW (off base d') v).readW base 64 = m.readW base 64 := by
  have := word_ww m base v (d := 0) (d' := d') (.inl h) (by omega) hd'
  simp only [Bignum.X86_64.word, off_zero] at this; exact this

theorem word0_wb (m : Mem) (base : Addr) {d' : Nat} (v : Byte) (h : 8 ≤ d') (hd' : d' < 2 ^ 64) :
    (m.writeW (off base d') v).readW base 64 = m.readW base 64 := by
  have := word_wb m base v (d := 0) (d' := d') (.inl h) (by omega) hd'
  simp only [Bignum.X86_64.word, off_zero] at this; exact this

theorem Outside.ww0 {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (v : BitVec 64)
    (h₁ : o = 0) (h₂ : 8 ≤ n) : Outside base o n m (m'.writeW base v) := by
  have := Outside.ww h (d := 0) v (by omega) (by omega) (by omega)
  rwa [off_zero] at this

/-- `p + i` with `p = base + d` as an offset of `base`. -/
theorem off_add (base : Addr) (d i : Nat) : off base d + BitVec.ofNat 64 i = off base (d + i) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

end VG.Proof.RsaPkcs1Enc.X86_64
