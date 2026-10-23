module

public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM: bytes written

Untrusted: everything here is checked by Lean. Target-independent facts
about the bytes at an address after writing bytes there (`writeBytes`), as
the copies and XORs of partial blocks leave them.
-/

@[expose] public section

namespace VG.Proof.AesGcm

open VG VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt]
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofNat_add]

/-- The bytes at `p`, after writing `xs` at `p + o`: the first `o`, then `xs`. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (o : Nat) (xs : List Byte) (h : o + xs.length < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 o) xs) p (o + xs.length) = bytesAt m p o ++ xs := by
  rw [bytesAt_add]
  congr 1
  · simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    exact writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp [bytesAt])
    intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), h₁, ite_true,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some]

/-- The bytes at `p`, after writing `xs` there. -/
theorem bytesAt_writeBytes_self (m : Mem) (p : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  have := bytesAt_writeBytes m p 0 xs (by omega)
  simp only [Nat.zero_add, BitVec.add_zero] at this
  rw [this]; rfl

/-- The bytes at `p` after writing `xs` there: `xs`, then what was there. -/
theorem bytesAt_writeBytes_prefix (m : Mem) (p : Addr) (xs : List Byte) {n : Nat} (hn : xs.length ≤ n)
    (h : n < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p n = xs ++ bytesAt m (p + BitVec.ofNat 64 xs.length) (n - xs.length) := by
  rw [show n = xs.length + (n - xs.length) by omega, bytesAt_add, bytesAt_writeBytes_self _ _ _ (by omega),
    Nat.add_sub_cancel_left]
  congr 1
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [writeBytes, BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := xs.length) (by omega), Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  simp [show ¬ (xs.length + i < xs.length) by omega]

/-- A write of `xs` at `q` keeps everything outside its `n` bytes. -/
theorem writeBytes_frame' (m : Mem) {q : Addr} {xs : List Byte} {n : Nat} (hn : xs.length = n) :
    Frame [⟨q, n⟩] m (writeBytes m q xs) :=
  writeBytes_frame m q xs (by rw [hn]; exact Region.contains_self _ _)

/-- A doubleword write is a write of its bytes, least significant first. -/
theorem writeW64_eq (m : Mem) (a : Addr) (v : BitVec 64) : m.writeW a v = writeBytes m a (Proof.Cmac.le8 v) := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, Proof.Cmac.length_le8]
  split
  · rename_i h
    rw [Proof.Cmac.getD_le8 _ h]
    simp
  · rfl

theorem le8_zero : Proof.Cmac.le8 0 = Spec.Gcm.zeros 8 := by decide

/-- Two zero doublewords are 16 zero bytes. -/
theorem write_zeros16 (m : Mem) (p : Addr) :
    (m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64) =
      writeBytes m p (Spec.Gcm.zeros 16) := by
  rw [writeW64_eq, writeW64_eq, le8_zero,
    show p + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (Spec.Gcm.zeros 8).length from rfl,
    writeBytes_append _ _ _ _ (by decide)]
  rfl

/-- After 16 zero bytes at `p`, `o ≤ 16` bytes `xs` there: `xs` padded with zeros. -/
theorem bytesAt_pad (m : Mem) (p : Addr) (xs : List Byte) (h : xs.length ≤ 16) :
    bytesAt (writeBytes (writeBytes m p (Spec.Gcm.zeros 16)) p xs) p 16 =
      xs ++ Spec.Gcm.zeros (16 - xs.length) := by
  rw [bytesAt_writeBytes_prefix _ _ _ h (by decide)]
  congr 1
  have h16 := bytesAt_writeBytes_self m p (Spec.Gcm.zeros 16) (by decide)
  rw [show (Spec.Gcm.zeros 16).length = xs.length + (16 - xs.length) by simp [Spec.Gcm.zeros]; omega,
    bytesAt_add] at h16
  have := congrArg (List.drop xs.length) h16
  rw [List.drop_left' (length_bytesAt ..)] at this
  rw [this]
  rw [Spec.Gcm.zeros, Spec.Gcm.zeros, List.drop_replicate]

end VG.Proof.AesGcm
