import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Mont.Mod

/-!
# Numbers of several words in memory, on any target

A number of `k` 64-bit words at offset `d` of the working space at `base`,
little-endian (`wordsVal`), and memory that changed only in a range of
offsets of `base` (`Outside`): what the Montgomery arithmetic of every
target reads and writes, the modulus in the working space (`ModOk`), and
slots apart from it and from each other (`Lay`).
-/

namespace VG.Proof.Mont

open VG VG.Impl.Mont

theorem pow64_succ (k : Nat) : 2 ^ (64 * (k + 1)) = 2 ^ 64 * 2 ^ (64 * k) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

/-- `x + 2⁶⁴ y < 2⁶⁴ X` for a word `x` and `y < X`. -/
theorem word_add_lt {x y X : Nat} (hx : x < 2 ^ 64) (hy : y < X) : x + 2 ^ 64 * y < 2 ^ 64 * X := by
  have : 2 ^ 64 * (y + 1) ≤ 2 ^ 64 * X := Nat.mul_le_mul_left _ hy
  rw [Nat.mul_succ] at this
  omega

/-- `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-- The word at `base + d`. -/
abbrev word (m : Mem) (base : Addr) (d : Nat) : BitVec 64 := m.readW (off base d) 64

/-- The `k` words at `base + d`, as a little-endian number. -/
def wordsVal (m : Mem) (base : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (word m base d).toNat + 2 ^ 64 * wordsVal m base (d + 8) k

theorem wordsVal_lt (m : Mem) (base : Addr) (d k : Nat) : wordsVal m base d k < 2 ^ (64 * k) := by
  induction k generalizing d with
  | zero => exact Nat.one_pos
  | succ k ih =>
    rw [wordsVal, pow64_succ]
    exact word_add_lt (word m base d).isLt (ih (d + 8))

/-! ## Memory outside a range of offsets -/

/-- The offset of `x` from `base`. -/
abbrev ofs (base x : Addr) : Nat := (x - base).toNat

/-- `m'` agrees with `m` but on the bytes at offsets `[o, o + n)` of `base`. -/
def Outside (base : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < o ∨ o + n ≤ ofs base x) → m' x = m x

theorem Outside.refl (base : Addr) (o n : Nat) (m : Mem) : Outside base o n m m := fun _ _ => rfl

theorem Outside.trans {base : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : Outside base o n m₁ m₂)
    (h₂ : Outside base o n m₂ m₃) : Outside base o n m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Outside.mono {base : Addr} {o n o' n' : Nat} {m m' : Mem} (h : Outside base o n m m')
    (h₁ : o' ≤ o) (h₂ : o + n ≤ o' + n') : Outside base o' n' m m' :=
  fun x hx => h x (by omega)

theorem ofs_off (base : Addr) {d i : Nat} (h : d + i < 2 ^ 64) :
    ofs base (off base d + BitVec.ofNat 64 i) = d + i := by
  simp only [ofs, off]
  rw [Offset.add_add, Mem.sub_ofNat_toNat base h]

/-- A word at an offset outside the bytes that changed. -/
theorem Outside.word {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 ≤ 2 ^ 64) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)).symm).symm

theorem Outside.wordsVal {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    {d k : Nat} (hd : d + 8 * k ≤ o ∨ o + n ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) :
    VG.Proof.Mont.wordsVal m' base d k = VG.Proof.Mont.wordsVal m base d k := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    simp only [VG.Proof.Mont.wordsVal]
    rw [h.word (by omega) (by omega), ih (by omega) (by omega)]

theorem writeW_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : d + 8 ≤ 2 ^ 64) :
    Outside base d 8 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

theorem word_writeW_self (m : Mem) (base : Addr) (d : Nat) (v : BitVec 64) :
    word (m.writeW (off base d) v) base d = v := Mem.readW_writeW_self64 _ _ _

theorem ofs_off0 (base : Addr) {d : Nat} (h : d < 2 ^ 64) : ofs base (off base d) = d :=
  Mem.sub_ofNat_toNat base h

theorem writeW8_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 8) (h : d + 1 ≤ 2 ^ 64) :
    Outside base d 1 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

theorem writeW8_self (m : Mem) (a : Addr) (v : BitVec 8) : (m.writeW a v) a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero,
    Nat.mul_zero, BitVec.setWidth_eq]
  exact BitVec.extractLsb'_eq_self

/-! ## The modulus -/

/-- The modulus `m`: its `n` words at `M.mo`, the temporary area at `M.tmp`,
in the working space and apart, and `M.minv = -m⁻¹ mod 2⁶⁴`. -/
structure ModOk (M : Mod) (size m : Nat) (mem : Mem) (base : Addr) : Prop where
  n0 : 0 < M.n
  n7 : M.n < 7
  mo : M.mo + 8 * M.n ≤ size
  tmp : M.tmp + 8 * M.n ≤ size
  sep : M.mo + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ M.mo
  val : wordsVal mem base M.mo M.n = m
  inv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0

/-! ## Slots -/

/-- The slots `Sl` (offsets of `n`-word numbers in a working space of `size`
bytes): any two are the same or apart, and each is apart from the modulus
and from the temporary area. -/
structure Lay (M : Mod) (size : Nat) (Sl : Nat → Prop) : Prop where
  le : ∀ x, Sl x → x + 8 * M.n ≤ size
  apart : ∀ x y, Sl x → Sl y → x ≠ y → x + 8 * M.n ≤ y ∨ y + 8 * M.n ≤ x
  mo : ∀ x, Sl x → x + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ x
  tmp : ∀ x, Sl x → x + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ x

/-- Slots on a grid: `d + 8 n i` for `lo ≤ i < hi`, with the modulus and the
temporary area on the grid below `lo`. -/
theorem Lay.grid {M : Mod} {size d lo hi imo itmp : Nat} (hmo : M.mo = d + 8 * M.n * imo)
    (htmp : M.tmp = d + 8 * M.n * itmp) (himo : imo < lo) (hitmp : itmp < lo)
    (hsize : d + 8 * M.n * hi ≤ size) :
    Lay M size fun x => ∃ i, lo ≤ i ∧ i < hi ∧ x = d + 8 * M.n * i := by
  have apart : ∀ i j, i ≠ j → d + 8 * M.n * i + 8 * M.n ≤ d + 8 * M.n * j ∨
      d + 8 * M.n * j + 8 * M.n ≤ d + 8 * M.n * i := by
    intro i j hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · have := Nat.mul_le_mul_left (8 * M.n) h
      rw [Nat.mul_succ] at this
      omega
    · have := Nat.mul_le_mul_left (8 * M.n) h
      rw [Nat.mul_succ] at this
      omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x ⟨i, -, hi', rfl⟩
    have := Nat.mul_le_mul_left (8 * M.n) hi'
    rw [Nat.mul_succ] at this
    omega
  · rintro x y ⟨i, -, -, rfl⟩ ⟨j, -, -, rfl⟩ hxy
    exact apart i j fun h => hxy (h ▸ rfl)
  · rintro x ⟨i, hi, -, rfl⟩
    rw [hmo]; exact apart i imo (by omega)
  · rintro x ⟨i, hi, -, rfl⟩
    rw [htmp]; exact apart i itmp (by omega)

/-- `t₀ + (t₀ m' mod 2⁶⁴) m ≡ 0 (mod 2⁶⁴)` when `m m' ≡ -1`. -/
theorem mont_low (t0 minv m : Nat) (h : (m * minv + 1) % 2 ^ 64 = 0) :
    (t0 + t0 * minv % 2 ^ 64 * m) % 2 ^ 64 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod (t0 * minv % 2 ^ 64), Nat.mod_mod, ← Nat.mul_mod,
    ← Nat.add_mod, show t0 + t0 * minv * m = t0 * (m * minv + 1) by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm minv m]; omega,
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

theorem wordsVal_succ_top (m : Mem) (base : Addr) (d k : Nat) :
    wordsVal m base d (k + 1) = wordsVal m base d k + 2 ^ (64 * k) * (word m base (d + 8 * k)).toNat := by
  induction k generalizing d with
  | zero => simp [wordsVal]
  | succ k ih =>
    rw [wordsVal, ih (d + 8), wordsVal, pow64_succ, Nat.mul_add, Nat.mul_assoc,
      show d + 8 + 8 * k = d + 8 * (k + 1) by omega]
    omega

/-- What `csub` computes: the number `T + X top < 2m` below `m`, given its
difference with `m`, `D + m = T + X b`, and the selection by the borrow. -/
theorem csub_arith {T D top X m : Nat} {b : Bool} (hX : m < X) (hD : D < X)
    (hV : T + X * top < 2 * m) (he : D + m = T + X * b.toNat) :
    (if top < b.toNat then T else D) = (T + X * top) % m := by
  have htop : top ≤ 1 := by
    rcases Nat.lt_or_ge top 2 with h | h
    · omega
    · have : X * 2 ≤ X * top := Nat.mul_le_mul_left _ h
      omega
  rcases (by omega : top = 0 ∨ top = 1) with rfl | rfl <;> cases b <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at he hV ⊢
  · simp only [Nat.lt_irrefl, ite_false]
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [Nat.zero_lt_one, ite_true]
    rw [Nat.mod_eq_of_lt (by omega)]
  · omega
  · simp only [Nat.lt_irrefl, ite_false]
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem m_pos {m B : Nat} (hB : B < m) : 0 < m := by omega

end VG.Proof.Mont
