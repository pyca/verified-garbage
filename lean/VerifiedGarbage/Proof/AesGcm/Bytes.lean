module

public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Aes
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

end VG.Proof.AesGcm
