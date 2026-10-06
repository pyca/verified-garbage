import VerifiedGarbage.Spec.RsaPkcs1Sig
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PKCS1-v1_5: bytes in memory

What the proofs of the encoding on every target say of the bytes they read
and write (`Spec.Rsa.bytesAt`, `writeBytes`), whatever the ISA.
-/

namespace VG.Proof.RsaPkcs1Sig

open VG VG.WriteBytes Spec.RsaPkcs1Sig

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem bytesAt_take_succ (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).take (i + 1) =
      (Spec.Rsa.bytesAt m p n).take i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp only [Spec.Rsa.bytesAt]
  rw [← List.map_take, ← List.map_take, List.take_range, List.take_range, Nat.min_eq_left (by omega),
    Nat.min_eq_left (by omega), List.range_succ, List.map_append]
  rfl

/-- The byte at `a`, outside the buffer, is kept by writing it. -/
theorem writeBytes_out (m : Mem) (q a : Addr) (xs : List Byte) (k : Nat)
    (hd : ∀ i < k, a ≠ q + BitVec.ofNat 64 i) (hl : xs.length ≤ k) : writeBytes m q xs a = m a := by
  simp only [writeBytes]
  split
  · rename_i h
    exact absurd (show a = q + BitVec.ofNat 64 (a - q).toNat by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega) (hd _ (by omega))
  · rfl

/-- Writing `xs` at `q` changes memory only there. -/
theorem frame_writeBytes (m : Mem) (q : Addr) (xs : List Byte) :
    Frame [⟨q, xs.length⟩] m (writeBytes m q xs) := by
  intro x hx
  have h := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h
  simp only [writeBytes]
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' (by omega))]

/-- The bytes written. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) (hl : xs.length < 2 ^ 64) :
    Spec.Rsa.bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  rw [ite_eq_left_iff.mpr (fun h' => absurd h₂ h')]
  simp [List.getD_eq_getElem?_getD, h₂]

/-- Two addresses of disjoint regions differ. -/
theorem ne_of_disjoint {p q : Addr} {n k : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨q, k⟩) (hn : n ≤ 2 ^ 64)
    (hk : k ≤ 2 ^ 64) {j i : Nat} (hj : j < n) (hi : i < k) :
    p + BitVec.ofNat 64 j ≠ q + BitVec.ofNat 64 i := by
  intro h
  refine hd (p + BitVec.ofNat 64 j) ?_ ?_
  · simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; omega
  · rw [h]; simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; omega

/-- Bytes apart from those written. -/
theorem bytes_apart {m m' : Mem} {R W : Region} (hf : Frame [W] m m') (hd : R.Disjoint W) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' R.base R.len = Spec.Rsa.bytesAt m R.base R.len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := R) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
    hl (List.mem_range.mp hi)

/-- The last bytes of a string of bytes. -/
theorem bytesAt_drop (m : Mem) (p : Addr) (d n : Nat) :
    (Spec.Rsa.bytesAt m p (d + n)).drop d = Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 d) n := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h₁ h₂
  simp only [List.getElem_drop, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, BitVec.add_assoc,
    ← BitVec.ofNat_add]

theorem prefix_length_le (h : Hash) : h.prefix.length + h.len ≤ 83 := by cases h <;> decide

theorem len_pos (h : Hash) : 0 < h.len := by cases h <;> decide

theorem ofNat_succ (a : Addr) (n : Nat) :
    a + BitVec.ofNat 64 n + 1 = a + BitVec.ofNat 64 (n + 1) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp

end VG.Proof.RsaPkcs1Sig
