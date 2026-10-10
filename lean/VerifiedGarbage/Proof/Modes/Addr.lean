import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Spec.Aes

/-!
# Addresses at offsets, for the modes

Facts about the bytes at offsets of a base address, and in memory around
stores and frames, that the modes' proofs share, on any 64-bit target. Nothing here depends on a cipher or a
target.
-/

namespace VG.Proof.Modes

open VG
open VG.Spec.Aes (bytesAt)

theorem off_sub_toNat (B : Addr) {t e : Nat} (h : e ≤ t) (ht : t < 2 ^ 64) :
    (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat = t - e := by
  rw [VG.Offset.add_sub_add _ h, BitVec.toNat_ofNat]; omega

theorem off_sub_not (B : Addr) {t e n : Nat} (h : t < e ∨ e + n ≤ t) (ht : t < 2 ^ 64) (hn : 0 < n)
    (he : e + n ≤ 2 ^ 64) : ¬ (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat < n := by
  rw [VG.Offset.add_sub_add_left]; exact VG.Offset.not_lt_sub_ofNat h ht hn he

theorem not_contains_off (b : Addr) {t e n : Nat} (h : t < e ∨ e + n ≤ t) (ht : t < 2 ^ 64) (hn : 0 < n)
    (he : e + n ≤ 2 ^ 64) : ¬ (⟨b + BitVec.ofNat 64 e, n⟩ : Region).Contains (b + BitVec.ofNat 64 t) 1 := by
  simp only [Region.Contains]; intro hc; exact off_sub_not b h ht hn he (by omega)

/-- A byte of `A`'s area is not among the 8 at `B + e`. -/
theorem not_in_of_disjoint {A B : Addr} {n t e : Nat} (hsep : Region.Disjoint ⟨A, n⟩ ⟨B, n⟩) (ht : t < n)
    (he : e + 8 ≤ n) (hn : n < 2 ^ 64) : ¬ (A + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat < 8 :=
  fun h => hsep (A + BitVec.ofNat 64 t) (VG.Offset.contains_base A (by omega) (by omega))
    (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega))

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

/-- A byte of a little-endian word stored from the XOR of two loads. -/
theorem writeW_xor_apply (m m₁ m₂ : Mem) (a c e x : Addr) :
    m.writeW a (m₁.readW c 64 ^^^ m₂.readW e 64) x =
      if (x - a).toNat < 8 then m₁ (c + BitVec.ofNat 64 (x - a).toNat) ^^^ m₂ (e + BitVec.ofNat 64 (x - a).toNat)
      else m x := by
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq]
  split
  · rename_i h
    rw [BitVec.extractLsb'_xor, Mem.readW, Mem.readW, BitVec.setWidth_eq, BitVec.setWidth_eq,
      Mem.extractLsb'_read m₁ c (n := 8) h, Mem.extractLsb'_read m₂ e (n := 8) h]
  · rfl

/-- Bytes below a store. -/
theorem bytesAt_writeW_above (m : Mem) (P : Addr) {w : Nat} (v : BitVec w) {d n : Nat} (hn : n ≤ d)
    (hw : 0 < w / 8) (hd : d + w / 8 ≤ 2 ^ 64) :
    bytesAt (m.writeW (P + BitVec.ofNat 64 d) v) P n = bytesAt m P n := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ _
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, Mem.writeW]
  apply Mem.write_apply
  exact off_sub_not P (t := i) (e := d) (n := w / 8) (Or.inl (by omega)) (by omega) hw hd

/-- Bytes outside a frame. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ _
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  exact hf.bytes (R := ⟨p, n⟩) hd hn h₁

end VG.Proof.Modes
