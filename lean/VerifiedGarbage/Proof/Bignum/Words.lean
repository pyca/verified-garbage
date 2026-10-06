import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Spec.Rsa

/-!
# Multiword arithmetic: words in memory

Target-independent facts about the numbers the bignum code keeps in memory.
A number of `n` words at byte offset `d` from `base` is `wv m base d n`,
little-endian.

`Outside base o n m m'`: `m'` agrees with `m` but on the bytes at offsets
`[o, o + n)` of `base`, so a number elsewhere keeps its value
(`Outside.wv`).

And the arithmetic of words: carries (`addc_toNat`, `adc_toNat`), borrows
(`sbb_toNat`, `lt_of_borrow`), products (`mul_toNat`) and masks (`mask`,
`select_mask`).
-/

namespace VG.Proof.Bignum

open VG
open VG.Proof.Poly1305.Limbs64 (add_adc_toNat)


/-! ## Numbers in memory -/

/-- `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-- The word at `p + d`. -/
abbrev word (m : Mem) (p : Addr) (d : Nat) : BitVec 64 := m.readW (off p d) 64

/-- The `n` words at `p + d`, little-endian. -/
def wv (m : Mem) (p : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => wv m p d n + 2 ^ (64 * n) * (word m p (d + 8 * n)).toNat

theorem pow64_succ (k : Nat) : 2 ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by
  rw [Nat.mul_succ, Nat.pow_add]

theorem wv_lt (m : Mem) (p : Addr) (d n : Nat) : wv m p d n < 2 ^ (64 * n) := by
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih =>
    rw [wv, pow64_succ]
    have hw := (word m p (d + 8 * n)).isLt
    have : 2 ^ (64 * n) * (word m p (d + 8 * n)).toNat ≤ 2 ^ (64 * n) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_sub, Nat.mul_one] at this
    omega

theorem wv_congr {m m' : Mem} {p : Addr} {d n : Nat}
    (h : ∀ i < n, word m' p (d + 8 * i) = word m p (d + 8 * i)) : wv m' p d n = wv m p d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [wv]
    rw [ih fun i hi => h i (by omega), h n (by omega)]

/-- A number of `n + k` words is its low `n` words and its high `k` words. -/
theorem wv_add (m : Mem) (p : Addr) (d n k : Nat) :
    wv m p d (n + k) = wv m p d n + 2 ^ (64 * n) * wv m p (d + 8 * n) k := by
  induction k with
  | zero => simp [wv]
  | succ k ih =>
    rw [← Nat.add_assoc, wv, ih, wv, show 64 * (n + k) = 64 * n + 64 * k by omega, Nat.pow_add,
      show d + 8 * (n + k) = d + 8 * n + 8 * k by omega, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]

/-- A number is zero iff its words are. -/
theorem wv_eq_zero_iff (m : Mem) (p : Addr) (d n : Nat) :
    wv m p d n = 0 ↔ ∀ q < n, word m p (d + 8 * q) = 0 := by
  induction n with
  | zero => simp [wv]
  | succ n ih =>
    rw [wv]
    constructor
    · intro h q hq
      have h1 : wv m p d n = 0 := by omega
      have h2 : 2 ^ (64 * n) * (word m p (d + 8 * n)).toNat = 0 := by omega
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | hq
      · exact ih.mp h1 q hq
      · subst hq
        rcases Nat.mul_eq_zero.mp h2 with h | h
        · exact absurd h (Nat.ne_of_gt (Nat.two_pow_pos _))
        · exact BitVec.eq_of_toNat_eq h
    · intro h
      rw [ih.mpr fun q hq => h q (by omega), h n (by omega)]
      rfl

/-- A number whose words but word `i` are zero. -/
theorem wv_single (m : Mem) (p : Addr) (d : Nat) {i : Nat} :
    ∀ n, i < n → (∀ q < n, q ≠ i → word m p (d + 8 * q) = 0) →
      wv m p d n = (word m p (d + 8 * i)).toNat * 2 ^ (64 * i)
  | 0, hi, _ => absurd hi (by omega)
  | n + 1, hi, h => by
    rw [wv]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · rw [wv_single m p d n hi fun q hq hne => h q (by omega) hne, h n (by omega) (by omega)]
      simp
    · subst hi
      rw [(wv_eq_zero_iff m p d i).mpr fun q hq => h q (by omega) (by omega), Nat.zero_add, Nat.mul_comm]

/-! ## Addresses -/

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

theorem ofNat_mul8 (j : Nat) : BitVec.ofNat 64 j * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * j) := by
  rw [Nat.mul_comm, BitVec.ofNat_mul]

theorem ofInt_ofNat (d : Nat) : BitVec.ofInt 64 (Int.ofNat d) = BitVec.ofNat 64 d := by
  rw [Int.ofNat_eq_natCast, BitVec.ofInt_natCast]

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

theorem Outside.wv {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    {d k : Nat} (hd : d + 8 * k ≤ o ∨ o + n ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) :
    wv m' base d k = wv m base d k :=
  wv_congr fun i hi => h.word (by omega) (by omega)

theorem writeW_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : d + 8 ≤ 2 ^ 64) :
    Outside base d 8 m (m.writeW (off base d) v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem word_writeW_self (m : Mem) (base : Addr) (d : Nat) (v : BitVec 64) :
    word (m.writeW (off base d) v) base d = v := Mem.readW_writeW_self64 m _ v

/-- Writing word `n` of a number of `n + 1` words. -/
theorem wv_writeW_top (m : Mem) (base : Addr) (d n : Nat) (v : BitVec 64) (h : d + 8 * n + 8 ≤ 2 ^ 64) :
    wv (m.writeW (off base (d + 8 * n)) v) base d (n + 1) = wv m base d n + 2 ^ (64 * n) * v.toNat := by
  rw [wv, word_writeW_self, (writeW_outside m base v (by omega)).wv (Or.inl (Nat.le_refl _)) (by omega)]


/-! ## Carries, borrows, products and masks -/

/-- `lo + 2⁶⁴ hi = lo + c` with the carry into `hi`. -/
theorem addc_toNat (lo hi c : BitVec 64) (h : lo.toNat + c.toNat + 2 ^ 64 * hi.toNat < 2 ^ 128) :
    (lo + c).toNat + 2 ^ 64 * (hi + 0 +
      (BitVec.ofBool (decide (2 ^ 64 ≤ lo.toNat + c.toNat))).setWidth 64).toNat =
      lo.toNat + c.toNat + 2 ^ 64 * hi.toNat := by
  have := add_adc_toNat lo c hi 0 (by rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega)
  rwa [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at this

/-- The product `rdx:rax` of `mul`, as a number. -/
theorem mul_toNat (a b : BitVec 64) :
    (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat +
      2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat = a.toNat * b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hp : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a.toNat * b.toNat / 2 ^ 64) (by omega)]
  exact Nat.mod_add_div _ _

theorem mul_le (a b : BitVec 64) : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
  Nat.mul_le_mul (by have := a.isLt; omega) (by have := b.isLt; omega)


/-- The mask of a borrow, as `sbb rbp, rbp` leaves it. -/
def mask (c : Bool) : BitVec 64 := 0 - (BitVec.ofBool c).setWidth 64

theorem mask_false : mask false = 0 := rfl

theorem mask_true : mask true = BitVec.allOnes 64 := rfl

/-- `add rbp, rbp` sets the carry from the mask. -/
theorem cf_mask (c : Bool) : decide (2 ^ 64 ≤ (mask c).toNat + (mask c).toNat) = c := by
  cases c <;> decide

/-- `sbb`, as numbers: `a - b - c`, plus `2⁶⁴` if it borrows. -/
theorem sbb_toNat (a b : BitVec 64) (c : Bool) :
    (a - b - (BitVec.ofBool c).setWidth 64).toNat + b.toNat + c.toNat =
      a.toNat + 2 ^ 64 * (decide (a.toNat < b.toNat + c.toNat)).toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hc : ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by cases c <;> rfl
  have hc1 := Bool.toNat_le c
  rw [BitVec.toNat_sub, BitVec.toNat_sub, hc]
  by_cases h : a.toNat < b.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

/-- The selection: `((a ^ b) & m) ^ b` is `a` for the mask of `true`, `b`
for that of `false`. -/
theorem select_mask (a b : BitVec 64) (c : Bool) :
    ((a ^^^ b) &&& mask c) ^^^ b = if c then a else b := by
  cases c
  · simp [mask_false]
  · simp only [mask_true, BitVec.and_allOnes, ite_true]
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]


/-- `adc`, as numbers. -/
theorem adc_toNat (a b : BitVec 64) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 64).toNat + 2 ^ 64 *
      (decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)).toNat = a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hc : ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by cases c <;> rfl
  have hc1 := Bool.toNat_le c
  rw [BitVec.toNat_add, BitVec.toNat_add, hc]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega


theorem lt_of_borrow {X N d P : Nat} {c : Bool} (hd : d < P)
    (h : d + N = X + P * c.toNat) : c = decide (X < N) := by
  cases c <;> simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero] at h <;>
    (symm; simp only [decide_eq_true_eq, decide_eq_false_iff_not]) <;> omega


/-- Numbers at two places with the same words. -/
theorem wv_congr2 {m m' : Mem} {p p' : Addr} {d d' n : Nat}
    (h : ∀ i < n, word m' p' (d' + 8 * i) = word m p (d + 8 * i)) : wv m' p' d' n = wv m p d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [wv]
    rw [ih fun i hi => h i (by omega), h n (by omega)]


/-- `t₀ + (t₀ m' mod 2⁶⁴) m ≡ 0 (mod 2⁶⁴)` when `m m' ≡ -1`. -/
theorem mont_low (t0 minv m : Nat) (h : (m * minv + 1) % 2 ^ 64 = 0) :
    (t0 * minv % 2 ^ 64 * m + t0) % 2 ^ 64 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod (t0 * minv % 2 ^ 64), Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod,
    show t0 * minv * m + t0 = t0 * (m * minv + 1) by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm minv m],
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]


/-- A number of `w + 2` words: its low `w` words and the two above. -/
theorem wv_top2 (m : Mem) (B : Addr) (d w : Nat) :
    wv m B d (w + 2) = wv m B d w + 2 ^ (64 * w) *
      ((word m B (d + 8 * w)).toNat + 2 ^ 64 * (word m B (d + 8 * w + 8)).toNat) := by
  rw [show w + 2 = w + 1 + 1 from rfl, wv, wv, pow64_succ, show d + 8 * (w + 1) = d + 8 * w + 8 by omega]
  grind


theorem and_mask_toNat (x : BitVec 64) (c : Bool) : (x &&& mask c).toNat = if c then x.toNat else 0 := by
  cases c
  · simp [mask_false]
  · rw [mask_true, BitVec.and_allOnes]; rfl

theorem shr8_toNat (x : BitVec 64) : (x >>> 8).toNat = x.toNat / 256 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-! ## Words of a number -/

/-- A word of a number of `w` words. -/
theorem word_of_wv (m : Mem) (B : Addr) (ed w : Nat) {q : Nat} (hq : q < w) :
    (word m B (ed + 8 * q)).toNat = wv m B ed w / 2 ^ (64 * q) % 2 ^ 64 := by
  have h := wv_add m B ed q (w - q)
  rw [show q + (w - q) = w by omega] at h
  obtain ⟨r, hr⟩ : ∃ r, w - q = r + 1 := ⟨w - q - 1, by omega⟩
  rw [hr, show r + 1 = 1 + r by omega, wv_add, show (wv m B (ed + 8 * q) 1) = (word m B (ed + 8 * q)).toNat
    by simp [wv]] at h
  rw [h]
  have hl := wv_lt m B ed q
  have hw := (word m B (ed + 8 * q)).isLt
  rw [Nat.add_mul_div_left _ _ (by exact Nat.pow_pos (by decide)), Nat.div_eq_of_lt hl, Nat.zero_add,
    show 64 * 1 = 64 from rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw]

theorem out_ne {out : Addr} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (h : i ≠ j) :
    out + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j := by
  intro he
  apply h
  have h2 : BitVec.ofNat 64 i = BitVec.ofNat 64 j := by
    have := congrArg (fun x => x - out) he
    simpa only [Offset.add_sub_cancel_left] using this
  have := congrArg BitVec.toNat h2
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this


/-! ## Numbers from big-endian bytes -/

/-- OS2IP of the first `i` bytes. -/
def pre (bs : List Byte) (i : Nat) : Nat := Spec.Rsa.os2ip (bs.take i)

theorem pre_succ (bs : List Byte) {i : Nat} (hi : i < bs.length) :
    pre bs (i + 1) = 256 * pre bs i + (bs[i]).toNat := by
  unfold pre Spec.Rsa.os2ip
  rw [← List.take_concat_get hi, List.concat_eq_append, List.foldl_append]
  rfl

theorem pre_zero (bs : List Byte) : pre bs 0 = 0 := rfl

theorem pre_len (bs : List Byte) : pre bs bs.length = Spec.Rsa.os2ip bs := by
  unfold pre; rw [List.take_length]

theorem pow256 (a : Nat) : (256 : Nat) ^ (8 * a) = 2 ^ (64 * a) := by
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega

/-- Words that are the base-`2⁶⁴` digits of `V` make `V mod 2^(64 n)`. -/
theorem wv_digits {m : Mem} {B : Addr} {ed V : Nat} (n : Nat)
    (h : ∀ q < n, word m B (ed + 8 * q) = BitVec.ofNat 64 (V / 256 ^ (8 * q))) :
    wv m B ed n = V % 2 ^ (64 * n) := by
  induction n with
  | zero => simp [wv, Nat.mod_one]
  | succ n ih =>
    rw [wv, ih fun q hq => h q (by omega), h n (by omega), BitVec.toNat_ofNat, pow256,
      show 64 * (n + 1) = 64 * n + 64 by omega, Nat.pow_add, Nat.mod_mul]

theorem pre_lt (bs : List Byte) {i : Nat} (hi : i ≤ bs.length) : pre bs i < 256 ^ i := by
  induction i with
  | zero => exact Nat.one_pos
  | succ i ih =>
    rw [pre_succ bs (by omega), Nat.pow_succ]
    have := ih (by omega)
    have := (bs[i]'(by omega)).isLt
    omega


/-! ## Inverses and bits -/

/-- Negating an inverse: `a (-x) + 1 ≡ 0` from `a x ≡ 1 (mod 2⁶⁴)`. -/
theorem neg_inv {a x : Nat} (hx : x < 2 ^ 64) (h : ((a : Int) * x - 1) % (2 ^ 64 : Int) = 0) :
    (a * ((2 ^ 64 - x + 0) % 2 ^ 64) + 1) % 2 ^ 64 = 0 := by
  have hr : (((2 ^ 64 - x + 0) % 2 ^ 64 : Nat) : Int) % 2 ^ 64 = -(x : Int) % 2 ^ 64 := by
    rw [Int.natCast_emod, show ((2 ^ 64 : Nat) : Int) = 2 ^ 64 from rfl, Int.emod_emod]
    omega
  have h2 : ((a * ((2 ^ 64 - x + 0) % 2 ^ 64) + 1 : Nat) : Int) % 2 ^ 64 =
      (-((a : Int) * x - 1)) % 2 ^ 64 := by
    rw [Int.natCast_add, Int.natCast_mul, Int.add_emod, Int.mul_emod, hr, ← Int.mul_emod,
      ← Int.add_emod]
    congr 1
    rw [Int.mul_neg]
    omega
  have h3 : (-((a : Int) * x - 1)) % 2 ^ 64 = 0 :=
    Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr (Int.dvd_of_emod_eq_zero h))
  have h4 := h2.trans h3
  change ((a * ((2 ^ 64 - x + 0) % 2 ^ 64) + 1 : Nat) : Int) % ((2 ^ 64 : Nat) : Int) = 0 at h4
  rw [← Int.natCast_emod] at h4
  exact Int.ofNat_inj.mp h4


theorem div_pow_succ (T j : Nat) : T / 2 ^ j / 2 = T / 2 ^ (j + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]


theorem wv_mod64 (m : Mem) (p : Addr) (d : Nat) {n : Nat} (hn : 1 ≤ n) :
    wv m p d n % 2 ^ 64 = (word m p d).toNat := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp [wv, Nat.mod_eq_of_lt (word m p d).isLt]
    · rw [wv, Nat.add_mod, ih hn', show 64 * n = 64 + 64 * (n - 1) by omega, Nat.pow_add, Nat.mul_assoc,
        Nat.mul_mod_right, Nat.add_zero, Nat.mod_eq_of_lt (word m p d).isLt]

end VG.Proof.Bignum
