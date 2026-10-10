import VerifiedGarbage.Spec.Idea
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# IDEA: words and bytes in memory

Target-independent facts about the memory layouts of `Spec/Idea.lean`: a
subkey is two bytes of a little-endian quadword (`word_read`,
`scheduleAt_getD`), a block's words are two big-endian bytes each
(`decodeBlock_blockAt`), byte writes within a block (`write8_apply`), and
the blocks of an ECB buffer (`block_contains`, `blocks_disjoint`).
-/

namespace VG.Proof.Idea

open VG

theorem extract16 (x : BitVec 64) (s : Nat) :
    x.extractLsb' s 16 = x.extractLsb' (s + 8) 8 ++ x.extractLsb' s 8 := by
  ext i hi
  rw [BitVec.getElem_extractLsb', BitVec.getElem_append]
  by_cases h : i < 8
  · simp [h, BitVec.getElem_extractLsb']
  · simp only [h, ↓reduceDIte, BitVec.getElem_extractLsb']
    congr 1; omega_arith

/-- Word `k` (16 bits) of a little-endian quadword in memory. -/
theorem word_read (m : Mem) (a : Addr) (k : Nat) (hk : k < 4) :
    ((m.readW a 64) >>> (16 * k)).setWidth 16 =
      m (a + BitVec.ofNat 64 (2 * k + 1)) ++ m (a + BitVec.ofNat 64 (2 * k)) := by
  rw [← Mem.extractLsb'_read m a (n := 8) (j := 2 * k + 1) (by omega_arith),
    ← Mem.extractLsb'_read m a (n := 8) (j := 2 * k) (by omega_arith)]
  show (m.readW a 64).extractLsb' (16 * k) 16 = _
  rw [extract16, show 16 * k + 8 = 8 * (2 * k + 1) by omega_arith, show 16 * k = 8 * (2 * k) by omega_arith]
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

/-- The low word of a little-endian quadword in memory. -/
theorem word_read0 (m : Mem) (a : Addr) :
    (m.readW a 64).setWidth 16 = m (a + 1) ++ m a := by
  have h := word_read m a 0 (by decide)
  simp only [Nat.mul_zero, BitVec.ushiftRight_zero, Nat.zero_add, BitVec.add_zero] at h
  exact h

theorem scheduleAt_getD (m : Mem) (p : Addr) {k : Nat} (hk : k < 52) :
    (Spec.Idea.scheduleAt m p).getD k 0 =
      m (p + BitVec.ofNat 64 (2 * k + 1)) ++ m (p + BitVec.ofNat 64 (2 * k)) := by
  simp [Spec.Idea.scheduleAt, Vector.getD, hk]

/-- Subkey `k` (at most 48) is the low word of the quadword at `p + 2k`. -/
theorem subkey_read (m : Mem) (p : Addr) {k : Nat} (hk : k < 52) :
    (m.readW (p + BitVec.ofNat 64 (2 * k)) 64).setWidth 16 = (Spec.Idea.scheduleAt m p).getD k 0 := by
  rw [word_read0, scheduleAt_getD m p hk, ← Offset.add_ofNat_add_ofNat]
  rfl

/-- Subkeys `48 + j` are the words of the quadword at `p + 96`. -/
theorem subkey_read96 (m : Mem) (p : Addr) {j : Nat} (hj : j < 4) :
    ((m.readW (p + BitVec.ofNat 64 96) 64) >>> (16 * j)).setWidth 16 =
      (Spec.Idea.scheduleAt m p).getD (48 + j) 0 := by
  rw [word_read _ _ _ hj, scheduleAt_getD m p (by omega_arith), Offset.add_ofNat_add_ofNat,
    Offset.add_ofNat_add_ofNat, show 96 + (2 * j + 1) = 2 * (48 + j) + 1 by omega_arith,
    show 96 + 2 * j = 2 * (48 + j) by omega_arith]

/-- Word `k` of a block in memory. -/
theorem decodeBlock_blockAt (m : Mem) (a : Addr) {k : Nat} (hk : k < 4) :
    (Spec.Idea.decodeBlock (Spec.Idea.blockAt m a)).getD k 0 =
      m (a + BitVec.ofNat 64 (2 * k)) ++ m (a + BitVec.ofNat 64 (2 * k + 1)) := by
  simp [Spec.Idea.decodeBlock, Spec.Idea.blockAt, Vector.getD, hk, show 2 * k < 8 by omega_arith,
    show 2 * k + 1 < 8 by omega_arith]

/-- A byte written at offset `j` of a block, read at offset `i`. -/
theorem write8_apply (m : Mem) (a : Addr) (v : BitVec 8) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (m.writeW (a + BitVec.ofNat 64 j) v) (a + BitVec.ofNat 64 i) =
      if i = j then v else m (a + BitVec.ofNat 64 i) := by
  have hd : ((a + BitVec.ofNat 64 i) - (a + BitVec.ofNat 64 j)).toNat = (i + 2 ^ 64 - j) % 2 ^ 64 := by
    rw [Offset.add_sub_add_left, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  simp only [Mem.writeW, Mem.write, hd]
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte]
    ext k hk
    simp
  · simp only [h, ↓reduceIte, ite_eq_right_iff]
    intro h'; omega_arith

/-- Byte `i` of an encoded block. -/
theorem encodeBlock_get (x : Spec.Idea.State) {i : Nat} (hi : i < 8) :
    (Spec.Idea.encodeBlock x)[i] = ((x.getD (i / 2) 0) >>> (8 * (1 - i % 2))).setWidth 8 := by
  simp [Spec.Idea.encodeBlock]

/-- Word `h` (16 bits) of a little-endian 32-bit word in memory, zero-extended. -/
theorem word_read32 (m : Mem) (a : Addr) (h : Nat) (hh : h < 2) :
    (((m.readW a 32).setWidth 64) >>> (16 * h)).setWidth 16 =
      m (a + BitVec.ofNat 64 (2 * h + 1)) ++ m (a + BitVec.ofNat 64 (2 * h)) := by
  rw [← Mem.extractLsb'_read m a (n := 4) (j := 2 * h + 1) (by omega_arith),
    ← Mem.extractLsb'_read m a (n := 4) (j := 2 * h) (by omega_arith)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', Mem.readW, Nat.reduceDiv]
  by_cases h8 : i < 8
  · simp [h8, hi, show 16 * h + i = 8 * (2 * h) + i by omega_arith,
      show 8 * (2 * h) + i < 32 by omega_arith, show 8 * (2 * h) + i < 64 by omega_arith]
  · simp [h8, hi, show i - 8 < 8 by omega_arith, show 16 * h + i = 8 * (2 * h + 1) + (i - 8) by omega_arith,
      show 8 * (2 * h + 1) + (i - 8) < 32 by omega_arith, show 8 * (2 * h + 1) + (i - 8) < 64 by omega_arith]

/-- Subkeys `2k` and `2k + 1` are the words of the 32-bit word at `p + 4k`. -/
theorem subkey_read32 (m : Mem) (p : Addr) {k h : Nat} (hk : k < 26) (hh : h < 2) :
    (((m.readW (p + BitVec.ofNat 64 (4 * k)) 32).setWidth 64) >>> (16 * h)).setWidth 16 =
      (Spec.Idea.scheduleAt m p).getD (2 * k + h) 0 := by
  rw [word_read32 _ _ _ hh, scheduleAt_getD m p (by omega_arith), Offset.add_ofNat_add_ofNat,
    Offset.add_ofNat_add_ofNat, show 4 * k + (2 * h + 1) = 2 * (2 * k + h) + 1 by omega_arith,
    show 4 * k + 2 * h = 2 * (2 * k + h) by omega_arith]

theorem read_one (m : Mem) (a : Addr) : m.read a 1 = m a := by
  apply BitVec.eq_of_toNat_eq
  simp only [Mem.read, BitVec.toNat_append]
  simp

/-- A byte written (by `Mem.write`) at offset `j` of a block, read at offset `i`. -/
theorem write1_apply (m : Mem) (a : Addr) (v : BitVec 8) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (m.write (a + BitVec.ofNat 64 j) 1 v) (a + BitVec.ofNat 64 i) =
      if i = j then v else m (a + BitVec.ofNat 64 i) := by
  have h := write8_apply m a v hi hj
  simpa only [Mem.writeW, BitVec.setWidth_eq] using h

/-! ## Blocks in a frame -/

/-- The bytes of a region disjoint from a frame's regions are unchanged. -/
theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    ∀ i < n, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

/-- Bytes `i … i + k` of block `j` of `n` at `a`. -/
theorem block_contains {a : Addr} {n j i k : Nat} (hj : j < n) (hi : i + k ≤ 8) (hk : 0 < k)
    (hb : 8 * n ≤ 2 ^ 64) :
    (⟨a, 8 * n⟩ : Region).Contains (a + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 i) k := by
  rw [Offset.add_ofNat_add_ofNat]
  exact Offset.contains_base a (by omega_arith) (by omega_arith)

theorem blocks_disjoint {a : Addr} {n j j' : Nat} (hj : j < n) (hj' : j' < n) (h : j ≠ j')
    (hb : 8 * n ≤ 2 ^ 64) :
    (⟨a + BitVec.ofNat 64 (8 * j'), 8⟩ : Region).Disjoint ⟨a + BitVec.ofNat 64 (8 * j), 8⟩ :=
  Offset.disjoint a (by omega_arith) (by omega_arith) (by omega_arith)

end VG.Proof.Idea
