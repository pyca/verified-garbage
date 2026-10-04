import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Rc2.PairMem

/-!
# Numbers as 32-bit words, on any target

The targets with 32-bit registers read the numbers of the working space as
32-bit words (`w32`, `val32`): `k` of them at an offset are the same bytes,
and the same number, as `k / 2` 64-bit words (`wordsVal_eq_val32`), in which
the other targets and the target-independent proofs state them. Their
stores, and memory that changed only in some ranges (`Outs`).
-/

namespace VG.Proof.Mont

open VG

/-- The 32-bit word at `base + d`. -/
abbrev w32 (m : Mem) (base : Addr) (d : Nat) : Nat := (m.readW (off base d) 32).toNat

/-- The `k` 32-bit words at `base + d`, as a little-endian number. -/
def val32 (m : Mem) (base : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => w32 m base d + 2 ^ 32 * val32 m base (d + 4) k

theorem pow32_succ (k : Nat) : 2 ^ (32 * (k + 1)) = 2 ^ 32 * 2 ^ (32 * k) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

theorem val32_lt (m : Mem) (base : Addr) (d k : Nat) : val32 m base d k < 2 ^ (32 * k) := by
  induction k generalizing d with
  | zero => exact Nat.one_pos
  | succ k ih =>
    rw [val32, pow32_succ]
    have h1 : w32 m base d < 2 ^ 32 := (m.readW (off base d) 32).isLt
    have h2 := ih (d + 4)
    have : 2 ^ 32 * (val32 m base (d + 4) k + 1) ≤ 2 ^ 32 * 2 ^ (32 * k) := Nat.mul_le_mul_left _ h2
    rw [Nat.mul_succ] at this
    omega

theorem val32_append (m : Mem) (base : Addr) (d j k : Nat) :
    val32 m base d (j + k) = val32 m base d j + 2 ^ (32 * j) * val32 m base (d + 4 * j) k := by
  induction j generalizing d with
  | zero => simp only [val32, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero]
  | succ j ih =>
    rw [Nat.add_right_comm, val32, ih, val32, pow32_succ, show d + 4 + 4 * j = d + 4 * (j + 1) by omega,
      Nat.mul_add, Nat.mul_assoc]
    omega

/-- The last word of a number. -/
theorem val32_succ (m : Mem) (base : Addr) (d k : Nat) :
    val32 m base d (k + 1) = val32 m base d k + 2 ^ (32 * k) * w32 m base (d + 4 * k) := by
  rw [val32_append, val32, val32, Nat.mul_zero, Nat.add_zero]

theorem val32_congr {m m' : Mem} {base : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ j < k, w32 m' base (d + 4 * j) = w32 m base (d + 4 * j)) →
      val32 m' base d k = val32 m base d k
  | 0, _ => rfl
  | k + 1, h => by
    rw [val32_succ, val32_succ, h k (Nat.lt_succ_self _), val32_congr fun j hj => h j (by omega)]

/-- A 64-bit word is two 32-bit words. -/
theorem word_eq_w32 (m : Mem) (base : Addr) (d : Nat) :
    (word m base d).toNat = w32 m base d + 2 ^ 32 * w32 m base (d + 4) := by
  rw [word, Rc2.Word32.read64_pair, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (m.readW (off base d) 32).isLt, Nat.shiftLeft_eq, Offset.add_add]
  simp only [w32, off]
  omega

/-- `n` 64-bit words are `2n` 32-bit words. -/
theorem wordsVal_eq_val32 (m : Mem) (base : Addr) (d n : Nat) :
    wordsVal m base d n = val32 m base d (2 * n) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [wordsVal, ih, word_eq_w32, show 2 * (n + 1) = 2 + 2 * n by omega, val32_append, val32, val32,
      val32, show d + 8 = d + 4 * 2 by omega, show (2 : Nat) ^ (32 * 2) = 2 ^ 64 by decide]
    omega

/-! ## Stores -/

/-- A 32-bit store at offset `o` leaves the words apart from it. -/
theorem w32_write_ne {m : Mem} {base : Addr} {size o d : Nat} (hn : base.toNat + size ≤ 2 ^ 32)
    (ho : o + 4 ≤ size) (hd : d + 4 ≤ size) (hsep : d + 4 ≤ o ∨ o + 4 ≤ d) (v : BitVec 32) :
    w32 (m.writeW (off base o) v) base d = w32 m base d := by
  rw [w32, Mem.readW_writeW_sep (Offset.sep base hsep (by omega) (by omega)) (by decide)]

/-- A 32-bit store at offset `o` is read back. -/
theorem w32_write_self (m : Mem) (base : Addr) (o : Nat) (v : BitVec 32) :
    w32 (m.writeW (off base o) v) base o = v.toNat := by
  rw [w32, Mem.readW_writeW_self32]

/-- A 32-bit store changes only its 4 bytes. -/
theorem writeW32_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 32) (h : d + 4 ≤ 2 ^ 64) :
    Outside base d 4 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

/-- A word at an offset outside the bytes that changed. -/
theorem Outside.w32 {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat} (hd : d + 4 ≤ o ∨ o + n ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    w32 m' base d = w32 m base d :=
  congrArg BitVec.toNat (Mem.readW_congr fun i hi => h _ (by rw [ofs_off base (by omega)]; omega))

theorem Outside.val32 {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    {d k : Nat} (hd : d + 4 * k ≤ o ∨ o + n ≤ d) (hd' : d + 4 * k ≤ 2 ^ 64) :
    val32 m' base d k = val32 m base d k :=
  val32_congr fun j hj => h.w32 (by omega) (by omega)

/-! ## Memory outside several ranges -/

/-- `m'` agrees with `m` but on the bytes at the ranges of offsets `rs`
(`(offset, length)`). -/
def Outs (base : Addr) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ x, (∀ r ∈ rs, ofs base x < r.1 ∨ r.1 + r.2 ≤ ofs base x) → m' x = m x

theorem Outs.refl (base : Addr) (rs : List (Nat × Nat)) (m : Mem) : Outs base rs m m := fun _ _ => rfl

theorem Outs.trans {base : Addr} {rs : List (Nat × Nat)} {m₁ m₂ m₃ : Mem} (h₁ : Outs base rs m₁ m₂)
    (h₂ : Outs base rs m₂ m₃) : Outs base rs m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Outs.mono {base : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    (hr : ∀ r ∈ rs, r ∈ rs' := by decide) : Outs base rs' m m' :=
  fun x hx => h x fun r h' => hx r (hr r h')

theorem Outs.of_outside {base : Addr} {o n : Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (h : Outside base o n m m') (hr : (o, n) ∈ rs) : Outs base rs m m' :=
  fun x hx => h x (hx _ hr)

/-- A number apart from every range that changed. -/
theorem Outs.val32 {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    {d k : Nat} (hd : ∀ r ∈ rs, d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 4 * k ≤ 2 ^ 64) :
    val32 m' base d k = val32 m base d k :=
  val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => h _ fun r hr => by
    have := hd r hr
    rw [ofs_off base (by omega)]; omega)

end VG.Proof.Mont
