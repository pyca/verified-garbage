import VerifiedGarbage.Proof.AesCfb8.Spec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CFB8: bytes in memory

The input block shifted left by a byte, with the next ciphertext byte
shifted in, as the functions write it (`shiftMem64`: two overlapping 64-bit
words and a byte; `shiftMem32`: four 32-bit words and a byte; `shiftMemX`:
two words, each the `extr` of two), and the data after one byte of it is
replaced (`bytesAt_set`).
-/

namespace VG.Proof.AesCfb8

open VG
open VG.Spec.Aes (bytesAt)

/-- Byte `x` after a 64-bit store at `a`. -/
theorem writeW64_apply (m : Mem) (a x : Addr) (v : BitVec 64) :
    m.writeW a v x = if (x - a).toNat < 8 then v.extractLsb' (8 * (x - a).toNat) 8 else m x := rfl

/-- Byte `x` after a byte store at `a`. -/
theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    m.writeW a v x = if (x - a).toNat < 1 then v.extractLsb' (8 * (x - a).toNat) 8 else m x := rfl

theorem extractLsb'_readW64 (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    (m.readW a 64).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) :=
  Mem.extractLsb'_read m a (n := 8) hj

/-- The block at `P` shifted left by a byte, with `c` shifted in: the
words at `P + 1` and `P + 8`, loaded first, stored at `P` and `P + 7`, and
`c` at `P + 15`. -/
def shiftMem64 (m : Mem) (P : Addr) (c : Byte) : Mem :=
  ((m.writeW P (m.readW (P + BitVec.ofNat 64 1) 64)).writeW (P + BitVec.ofNat 64 7)
    (m.readW (P + BitVec.ofNat 64 8) 64)).writeW (P + BitVec.ofNat 64 15) c

theorem shiftMem64_apply (m : Mem) (P : Addr) (c : Byte) {i : Nat} (hi : i < 16) :
    shiftMem64 m P c (P + BitVec.ofNat 64 i) = if i = 15 then c else m (P + BitVec.ofNat 64 (i + 1)) := by
  have h0 : (P + BitVec.ofNat 64 i - P).toNat = i := Mem.sub_ofNat_toNat P (by omega)
  have h7 := Offset.sub_toNat' P (d := 7) (e := i) (by decide) (by omega)
  have h15 := Offset.sub_toNat' P (d := 15) (e := i) (by decide) (by omega)
  simp only [shiftMem64, writeW64_apply, writeW8_apply]
  by_cases e15 : i = 15
  · subst e15
    have t15 : (P + BitVec.ofNat 64 15 - (P + BitVec.ofNat 64 15)).toNat = 0 := by rw [h15]; decide
    simp only [t15, Nat.zero_lt_one, Nat.mul_zero, ↓reduceIte]
    exact BitVec.extractLsb'_eq_self
  have t15 : ¬ (P + BitVec.ofNat 64 i - (P + BitVec.ofNat 64 15)).toNat < 1 := by rw [h15]; split <;> omega
  simp only [t15, e15, ↓reduceIte]
  by_cases e7 : 7 ≤ i
  · have t7 : (P + BitVec.ofNat 64 i - (P + BitVec.ofNat 64 7)).toNat = i - 7 := by
      rw [h7]; simp only [e7, ↓reduceIte]
    simp only [t7, show i - 7 < 8 by omega, ↓reduceIte]
    rw [extractLsb'_readW64 _ _ (by omega), Offset.add_add_eq _ (c := i + 1) (by omega)]
  · have t7 : ¬ (P + BitVec.ofNat 64 i - (P + BitVec.ofNat 64 7)).toNat < 8 := by rw [h7]; split <;> omega
    simp only [t7, h0, show i < 8 by omega, ↓reduceIte]
    rw [extractLsb'_readW64 _ _ (by omega), Offset.add_add_eq _ (c := i + 1) (by omega)]

theorem shiftMem64_bytes (m : Mem) (P : Addr) (c : Byte) :
    bytesAt (shiftMem64 m P c) P 16 = (bytesAt m P 16).tail ++ [c] := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ _
  have hi : i < 16 := by simpa [bytesAt] using h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, shiftMem64_apply m P c hi]
  by_cases e : i = 15
  · subst e; simp
  · simp only [e, ↓reduceIte]
    rw [List.getElem_append_left (by simp; omega)]
    simp

theorem shiftMem64_frame (m : Mem) (P : Addr) (c : Byte) : Frame [⟨P, 16⟩] m (shiftMem64 m P c) :=
  (((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base P (d := 0) (n := 8) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base P (d := 7) (n := 8) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base P (d := 15) (n := 1) (k := 16) (by decide) (by decide))

/-! ## With 32-bit words -/

/-- Byte `x` after a 32-bit store at `a`. -/
theorem writeW32_apply (m : Mem) (a x : Addr) (v : BitVec 32) :
    m.writeW a v x = if (x - a).toNat < 4 then v.extractLsb' (8 * (x - a).toNat) 8 else m x := rfl

theorem extractLsb'_readW32 (m : Mem) (a : Addr) {j : Nat} (hj : j < 4) :
    (m.readW a 32).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) :=
  Mem.extractLsb'_read m a (n := 4) hj

/-- The block at `P` shifted left by a byte, with `c` shifted in: the words
at `P + 1`, `P + 5`, `P + 9` and `P + 12`, loaded first, stored at `P`,
`P + 4`, `P + 8` and `P + 11`, and `c` at `P + 15`. -/
def shiftMem32 (m : Mem) (P : Addr) (c : Byte) : Mem :=
  ((((m.writeW P (m.readW (P + BitVec.ofNat 64 1) 32)).writeW (P + BitVec.ofNat 64 4)
    (m.readW (P + BitVec.ofNat 64 5) 32)).writeW (P + BitVec.ofNat 64 8)
    (m.readW (P + BitVec.ofNat 64 9) 32)).writeW (P + BitVec.ofNat 64 11)
    (m.readW (P + BitVec.ofNat 64 12) 32)).writeW (P + BitVec.ofNat 64 15) c

theorem shiftMem32_apply (m : Mem) (P : Addr) (c : Byte) {i : Nat} (hi : i < 16) :
    shiftMem32 m P c (P + BitVec.ofNat 64 i) = if i = 15 then c else m (P + BitVec.ofNat 64 (i + 1)) := by
  have h0 : (P + BitVec.ofNat 64 i - P).toNat = i := Mem.sub_ofNat_toNat P (by omega)
  have h4 := Offset.sub_toNat' P (d := 4) (e := i) (by decide) (by omega)
  have h8 := Offset.sub_toNat' P (d := 8) (e := i) (by decide) (by omega)
  have h11 := Offset.sub_toNat' P (d := 11) (e := i) (by decide) (by omega)
  have h15 := Offset.sub_toNat' P (d := 15) (e := i) (by decide) (by omega)
  simp only [shiftMem32, writeW32_apply, writeW8_apply]
  by_cases e15 : i = 15
  · subst e15
    have t15 : (P + BitVec.ofNat 64 15 - (P + BitVec.ofNat 64 15)).toNat = 0 := by rw [h15]; decide
    simp only [t15, Nat.zero_lt_one, Nat.mul_zero, ↓reduceIte]
    exact BitVec.extractLsb'_eq_self
  have t15 : ¬ (P + BitVec.ofNat 64 i - (P + BitVec.ofNat 64 15)).toNat < 1 := by rw [h15]; split <;> omega
  simp only [t15, e15, ↓reduceIte]
  by_cases e11 : 11 ≤ i
  · have t11 : (P + BitVec.ofNat 64 i - (P + BitVec.ofNat 64 11)).toNat = i - 11 := by
      rw [h11]; simp only [e11, ↓reduceIte]
    simp only [t11, show i - 11 < 4 by omega, ↓reduceIte]
    rw [extractLsb'_readW32 _ _ (by omega), Offset.add_add_eq _ (c := i + 1) (by omega)]
  have t11 : ¬ (P + BitVec.ofNat 64 i - (P + BitVec.ofNat 64 11)).toNat < 4 := by rw [h11]; split <;> omega
  simp only [t11, ↓reduceIte]
  by_cases e8 : 8 ≤ i
  · have t8 : (P + BitVec.ofNat 64 i - (P + BitVec.ofNat 64 8)).toNat = i - 8 := by
      rw [h8]; simp only [e8, ↓reduceIte]
    simp only [t8, show i - 8 < 4 by omega, ↓reduceIte]
    rw [extractLsb'_readW32 _ _ (by omega), Offset.add_add_eq _ (c := i + 1) (by omega)]
  have t8 : ¬ (P + BitVec.ofNat 64 i - (P + BitVec.ofNat 64 8)).toNat < 4 := by rw [h8]; split <;> omega
  simp only [t8, ↓reduceIte]
  by_cases e4 : 4 ≤ i
  · have t4 : (P + BitVec.ofNat 64 i - (P + BitVec.ofNat 64 4)).toNat = i - 4 := by
      rw [h4]; simp only [e4, ↓reduceIte]
    simp only [t4, show i - 4 < 4 by omega, ↓reduceIte]
    rw [extractLsb'_readW32 _ _ (by omega), Offset.add_add_eq _ (c := i + 1) (by omega)]
  have t4 : ¬ (P + BitVec.ofNat 64 i - (P + BitVec.ofNat 64 4)).toNat < 4 := by rw [h4]; split <;> omega
  simp only [t4, h0, show i < 4 by omega, ↓reduceIte]
  rw [extractLsb'_readW32 _ _ (by omega), Offset.add_add_eq _ (c := i + 1) (by omega)]

theorem shiftMem32_bytes (m : Mem) (P : Addr) (c : Byte) :
    bytesAt (shiftMem32 m P c) P 16 = (bytesAt m P 16).tail ++ [c] := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ _
  have hi : i < 16 := by simpa [bytesAt] using h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, shiftMem32_apply m P c hi]
  by_cases e : i = 15
  · subst e; simp
  · simp only [e, ↓reduceIte]
    rw [List.getElem_append_left (by simp; omega)]
    simp

theorem shiftMem32_frame (m : Mem) (P : Addr) (c : Byte) : Frame [⟨P, 16⟩] m (shiftMem32 m P c) :=
  (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base P (d := 0) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base P (d := 4) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base P (d := 8) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base P (d := 11) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base P (d := 15) (n := 1) (k := 16) (by decide) (by decide))

/-! ## With `extr` -/

/-- Byte `j` of the 64 bits above the low byte of `x ++ y`. -/
theorem extr_byte (x y : BitVec 64) {j : Nat} (hj : j < 8) :
    ((x ++ y).extractLsb' 8 64).extractLsb' (8 * j) 8 =
      if j < 7 then y.extractLsb' (8 * (j + 1)) 8 else x.extractLsb' 0 8 := by
  split
  · ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp only [show 8 * j + k < 64 by omega, decide_true, Bool.true_and, show 8 + (8 * j + k) < 64 by omega,
      ↓reduceIte]
    congr 1; omega
  · ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp only [show 8 * j + k < 64 by omega, decide_true, Bool.true_and, show ¬ (8 + (8 * j + k) < 64) by omega,
      ↓reduceIte]
    congr 1; omega

/-- The block at `P` shifted left by a byte, with `c` shifted in, as `extr`
of its two words loaded first: the high 64 bits of `w₁ : w₀` and of
`c : w₁`, from bit 8. -/
def shiftMemX (m : Mem) (P : Addr) (c : Byte) : Mem :=
  (m.writeW P ((m.readW (P + BitVec.ofNat 64 8) 64 ++ m.readW P 64).extractLsb' 8 64)).writeW
    (P + BitVec.ofNat 64 8) ((c.setWidth 64 ++ m.readW (P + BitVec.ofNat 64 8) 64).extractLsb' 8 64)

theorem shiftMemX_apply (m : Mem) (P : Addr) (c : Byte) {i : Nat} (hi : i < 16) :
    shiftMemX m P c (P + BitVec.ofNat 64 i) = if i = 15 then c else m (P + BitVec.ofNat 64 (i + 1)) := by
  have h0 : (P + BitVec.ofNat 64 i - P).toNat = i := Mem.sub_ofNat_toNat P (by omega)
  have h8 := Offset.sub_toNat' P (d := 8) (e := i) (by decide) (by omega)
  simp only [shiftMemX, writeW64_apply]
  by_cases e8 : 8 ≤ i
  · have t8 : (P + BitVec.ofNat 64 i - (P + BitVec.ofNat 64 8)).toNat = i - 8 := by
      rw [h8]; simp only [e8, ↓reduceIte]
    simp only [t8, show i - 8 < 8 by omega, ↓reduceIte, extr_byte _ _ (show i - 8 < 8 by omega)]
    by_cases e15 : i = 15
    · subst e15
      simp only [Nat.reduceSub, Nat.lt_irrefl, ↓reduceIte]
      ext k hk; simp [hk]; omega
    · simp only [show i - 8 < 7 by omega, e15, ↓reduceIte]
      rw [extractLsb'_readW64 _ _ (by omega), Offset.add_add_eq _ (c := i + 1) (by omega)]
  · have t8 : ¬ (P + BitVec.ofNat 64 i - (P + BitVec.ofNat 64 8)).toNat < 8 := by rw [h8]; split <;> omega
    simp only [t8, h0, show i < 8 by omega, ↓reduceIte, extr_byte _ _ (show i < 8 by omega),
      show ¬ i = 15 by omega]
    by_cases e7 : i < 7
    · simp only [e7, ↓reduceIte]
      rw [extractLsb'_readW64 _ _ (by omega)]
    · simp only [e7, ↓reduceIte]
      have e := extractLsb'_readW64 m (P + BitVec.ofNat 64 8) (j := 0) (by decide)
      simp only [Nat.mul_zero, BitVec.add_zero] at e
      rw [e, show i + 1 = 8 by omega]

theorem shiftMemX_bytes (m : Mem) (P : Addr) (c : Byte) :
    bytesAt (shiftMemX m P c) P 16 = (bytesAt m P 16).tail ++ [c] := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ _
  have hi : i < 16 := by simpa [bytesAt] using h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, shiftMemX_apply m P c hi]
  by_cases e : i = 15
  · subst e; simp
  · simp only [e, ↓reduceIte]
    rw [List.getElem_append_left (by simp; omega)]
    simp

theorem shiftMemX_frame (m : Mem) (P : Addr) (c : Byte) : Frame [⟨P, 16⟩] m (shiftMemX m P c) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base P (d := 0) (n := 8) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base P (d := 8) (n := 8) (k := 16) (by decide) (by decide))

/-- The bytes at `P` after a step that changed byte `k` of them and nothing
else among them. -/
theorem bytesAt_set {m m' : Mem} {P : Addr} {n k : Nat}
    (h : ∀ j < n, j ≠ k → m' (P + BitVec.ofNat 64 j) = m (P + BitVec.ofNat 64 j)) :
    bytesAt m' P n = (bytesAt m P n).set k (m' (P + BitVec.ofNat 64 k)) := by
  apply List.ext_getElem (by simp [bytesAt])
  intro j h₁ _
  have hj : j < n := by simpa [bytesAt] using h₁
  rw [List.getElem_set]
  by_cases e : k = j
  · subst e; simp [bytesAt]
  · simp only [e, ↓reduceIte, bytesAt, List.getElem_map, List.getElem_range]
    exact h j hj (Ne.symm e)

end VG.Proof.AesCfb8
