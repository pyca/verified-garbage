import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Impl.Rsa.AArch64.Crt

/-!
# Multiword arithmetic on AArch64: a product by rows

`mulRows`: `acc += a b` for `a` of `w_a` words (`x11`, `x13`) and `b` of
`w_b` words (`x9`, `x12`), row `i` adding `a_i b` at word `i` of the
accumulator (`mulAddRow`, at `x8`), for an accumulator of `w_a + w_b + 2`
words that starts below `2^(64 (w_b + 1))` (`mulRows_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Crt VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- The registers `mulRows` writes. -/
def mrRegs : List Reg := [.x1, .x2, .x3, .x4, .x8, .x11, .x13, .x14, .x16, .x17]

/-- After rows `0, …, i - 1`: `acc = A₀ + b (a mod 2^(64 i))`. -/
structure MRInv (s₀ : State) (B : Addr) (Z ea eb eA wa wb : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep mrRegs s₀ t
  x11 : t.gpr .x11 = off B (ea + 8 * i)
  x8 : t.gpr .x8 = off B (eA + 8 * i)
  out : Outside B eA (8 * (wa + wb + 2)) s₀.mem t.mem
  val : wv t.mem B eA (wa + wb + 2) = wv s₀.mem B eA (wa + wb + 2) + wv s₀.mem B eb wb * wv s₀.mem B ea i

/-- The accumulator's words as the words below `i`, the window of `k` words
at `i`, and the rest. -/
theorem wv_split3 (m : Mem) (B : Addr) (d i k L : Nat) (h : i + k ≤ L) :
    wv m B d L = wv m B d i + 2 ^ (64 * i) * (wv m B (d + 8 * i) k +
      2 ^ (64 * k) * wv m B (d + 8 * i + 8 * k) (L - i - k)) := by
  obtain ⟨r, rfl⟩ : ∃ r, L = i + (k + r) := ⟨L - i - k, by omega⟩
  rw [wv_add, wv_add, show i + (k + r) - i - k = r by omega, Nat.add_assoc d]

/-- The window a row adds to stays below `2^(64 (w_b + 2))`. -/
theorem row_fits {A W a b P : Nat} {wb i : Nat} (hA : A < 2 ^ (64 * (wb + 1))) (ha : a < 2 ^ 64)
    (hb : b < 2 ^ (64 * wb)) (hP : P < 2 ^ (64 * i)) (hle : 2 ^ (64 * i) * W ≤ A + b * P) :
    W + a * b < 2 ^ (64 * (wb + 2)) := by
  have hab : a * b ≤ (2 ^ 64 - 1) * 2 ^ (64 * wb) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : 2 ^ (64 * (wb + 2)) = 2 ^ (64 * wb) * 2 ^ 128 := by
    rw [show 64 * (wb + 2) = 64 * wb + 128 by omega, Nat.pow_add]
  have e2 : 2 ^ (64 * (wb + 1)) = 2 ^ (64 * wb) * 2 ^ 64 := by
    rw [show 64 * (wb + 1) = 64 * wb + 64 by omega, Nat.pow_add]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have : P = 0 := by simpa using hP
    subst this
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero] at hle
    rw [e1]; rw [e2] at hA
    have : 2 ^ (64 * wb) * 2 ^ 64 + (2 ^ 64 - 1) * 2 ^ (64 * wb) ≤ 2 ^ (64 * wb) * 2 ^ 128 := by
      rw [Nat.mul_comm (2 ^ 64 - 1), ← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by decide)
    omega
  · have hprod : b * P ≤ 2 ^ (64 * wb) * 2 ^ (64 * i) := Nat.mul_le_mul (by omega) (by omega)
    have hpi : 2 ^ (64 * (wb + 1)) ≤ 2 ^ (64 * wb) * 2 ^ (64 * i) := by
      rw [e2]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
    have hWlt : 2 ^ (64 * i) * W < 2 ^ (64 * i) * (2 * 2 ^ (64 * wb)) := by
      have : 2 ^ (64 * i) * (2 * 2 ^ (64 * wb)) = 2 ^ (64 * wb) * 2 ^ (64 * i) + 2 ^ (64 * wb) * 2 ^ (64 * i) := by
        grind
      omega
    have hW2 := Nat.lt_of_mul_lt_mul_left hWlt
    rw [e1]
    have : 2 * 2 ^ (64 * wb) + (2 ^ 64 - 1) * 2 ^ (64 * wb) ≤ 2 ^ (64 * wb) * 2 ^ 128 := by
      rw [Nat.mul_comm (2 ^ 64 - 1), Nat.mul_comm 2, ← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by decide)
    omega

theorem mrStep_ok {s₀ : State} {B : Addr} {Z ea eb eA wa wb : Nat} (hs : Scr s₀ B Z)
    (h9 : s₀.gpr .x9 = off B eb) (h12 : s₀.gpr .x12 = BitVec.ofNat 64 wb) (h7 : s₀.gpr .x7 = 0)
    (hwb : 1 ≤ wb) (hw : wa + wb < 2 ^ 30)
    (hA : eA + 8 * (wa + wb + 2) ≤ Z) (ha : ea + 8 * wa ≤ Z) (hb : eb + 8 * wb ≤ Z)
    (sa : ea + 8 * wa ≤ eA ∨ eA + 8 * (wa + wb + 2) ≤ ea) (sb : eb + 8 * wb ≤ eA ∨ eA + 8 * (wa + wb + 2) ≤ eb)
    (h0 : wv s₀.mem B eA (wa + wb + 2) < 2 ^ (64 * (wb + 1)))
    {i : Nat} (hi : i < wa) {t : State} (hI : MRInv s₀ B Z ea eb eA wa wb i t) :
    WP isa (.seq (.block [ld .x1 .x11, next .x11])
      (.seq mulAddRow (.block [next .x8, .subImm .x .x13 .x13 1]))) t
      fun t' => MRInv s₀ B Z ea eb eA wa wb (i + 1) t' ∧ t'.gpr .x13 = t.gpr .x13 - BitVec.ofNat 64 1 := by
  have hn := hs.nowrap
  have hk := hI.keep
  have t9 : t.gpr .x9 = off B eb := (hk.gpr .x9 (by decide)).trans h9
  have t12 : t.gpr .x12 = BitVec.ofNat 64 wb := (hk.gpr .x12 (by decide)).trans h12
  have t7 : t.gpr .x7 = 0 := (hk.gpr .x7 (by decide)).trans h7
  -- `x1 := a_i`.
  refine WP.seq (WP.mono (WP.keep [.x1, .x11] (Q := fun t₁ => t₁.gpr .x1 = word t.mem B (ea + 8 * i) ∧
      t₁.gpr .x11 = off B (ea + 8 * i + 8) ∧ t₁.mem = t.mem)
    (by brun [hI.x11, hI.scr.ld (show ea + 8 * i + 8 ≤ Z by omega)]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨hx1, h11, hm₁⟩, k₁⟩ => ?_)
  have hai : word t.mem B (ea + 8 * i) = word s₀.mem B (ea + 8 * i) := hI.out.word (by omega) (by omega)
  have fb : wv t.mem B eb wb = wv s₀.mem B eb wb := hI.out.wv (by omega) (by omega)
  -- The window and the rest of the accumulator.
  have sp := wv_split3 t.mem B eA i (wb + 2) (wa + wb + 2) (by omega)
  have hval := hI.val
  have hW : wv t.mem B (eA + 8 * i) (wb + 2) + (word s₀.mem B (ea + 8 * i)).toNat * wv s₀.mem B eb wb <
      2 ^ (64 * (wb + 2)) := by
    have hle : 2 ^ (64 * i) * wv t.mem B (eA + 8 * i) (wb + 2) ≤ wv t.mem B eA (wa + wb + 2) := by
      rw [sp]; have := Nat.mul_le_mul_left (2 ^ (64 * i)) (Nat.le_add_right (wv t.mem B (eA + 8 * i) (wb + 2))
        (2 ^ (64 * (wb + 2)) * wv t.mem B (eA + 8 * i + 8 * (wb + 2)) (wa + wb + 2 - i - (wb + 2))))
      omega
    rw [hval] at hle
    exact row_fits h0 (word s₀.mem B (ea + 8 * i)).isLt (wv_lt s₀.mem B eb wb) (wv_lt s₀.mem B ea i) hle
  have hs₁ := hI.scr.congr k₁.wr
  have t₁8 : t₁.gpr .x8 = off B (eA + 8 * i) := (k₁.gpr .x8 (by decide)).trans hI.x8
  refine WP.seq (WP.mono (mulAddRow_ok hs₁ t₁8 ((k₁.gpr .x9 (by decide)).trans t9)
    ((k₁.gpr .x12 (by decide)).trans t12) ((k₁.gpr .x7 (by decide)).trans t7) hwb (by omega) (by omega)
    (by omega) (by omega) (by rw [hm₁, hx1, hai, fb]; exact hW)) fun t₂ ⟨hv₂, ho₂, k₂⟩ => ?_)
  rw [hm₁, hx1, hai, fb] at hv₂
  rw [hm₁] at ho₂
  have t₂8 : t₂.gpr .x8 = off B (eA + 8 * i) := (k₂.gpr .x8 (by decide)).trans t₁8
  refine WP.mono (WP.keep [.x8, .x13] (Q := fun t' => t'.gpr .x8 = off B (eA + 8 * i + 8) ∧
      t'.gpr .x13 = t₂.gpr .x13 - BitVec.ofNat 64 1 ∧ t'.mem = t₂.mem)
    (by brun [t₂8]) (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨h8', h13', hm'⟩, k'⟩ => ⟨?_, ?_⟩
  · refine ⟨hI.scr.congr ((k₁.trans k₂).trans k').wr, ((hk.trans (k₁.trans k₂)).trans k').mono (by decide),
      ?_, ?_, ?_, ?_⟩
    · rw [(k₂.trans k').gpr .x11 (by decide), h11, Nat.mul_succ, Nat.add_assoc]
    · rw [h8', Nat.mul_succ, Nat.add_assoc]
    · rw [hm']
      exact hI.out.trans (ho₂.mono (by omega) (by omega))
    · -- The low words and the rest are as before.
      have sp' := wv_split3 t₂.mem B eA i (wb + 2) (wa + wb + 2) (by omega)
      have lo : wv t₂.mem B eA i = wv t.mem B eA i := ho₂.wv (Or.inl (by omega)) (by omega)
      have hi' : wv t₂.mem B (eA + 8 * i + 8 * (wb + 2)) (wa + wb + 2 - i - (wb + 2)) =
          wv t.mem B (eA + 8 * i + 8 * (wb + 2)) (wa + wb + 2 - i - (wb + 2)) :=
        ho₂.wv (Or.inr (by omega)) (by omega)
      rw [hm', sp', lo, hi', hv₂]
      have e : wv s₀.mem B ea (i + 1) = wv s₀.mem B ea i + 2 ^ (64 * i) * (word s₀.mem B (ea + 8 * i)).toNat := rfl
      rw [e]
      rw [sp] at hval
      grind
  · rw [h13', (k₁.trans k₂).gpr .x13 (by decide)]

/-- `acc += a b`, for an accumulator of `w_a + w_b + 2` words below
`2^(64 (w_b + 1))`. -/
theorem mulRows_ok {s : State} {B : Addr} {Z ea eb eA wa wb : Nat} (hs : Scr s B Z)
    (h11 : s.gpr .x11 = off B ea) (h9 : s.gpr .x9 = off B eb) (h13 : s.gpr .x13 = BitVec.ofNat 64 wa)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 wb) (h8 : s.gpr .x8 = off B eA) (h7 : s.gpr .x7 = 0)
    (hwa : 1 ≤ wa) (hwb : 1 ≤ wb) (hw : wa + wb < 2 ^ 30)
    (hA : eA + 8 * (wa + wb + 2) ≤ Z) (ha : ea + 8 * wa ≤ Z) (hb : eb + 8 * wb ≤ Z)
    (sa : ea + 8 * wa ≤ eA ∨ eA + 8 * (wa + wb + 2) ≤ ea) (sb : eb + 8 * wb ≤ eA ∨ eA + 8 * (wa + wb + 2) ≤ eb)
    (h0 : wv s.mem B eA (wa + wb + 2) < 2 ^ (64 * (wb + 1))) :
    WP isa mulRows s fun t =>
      wv t.mem B eA (wa + wb + 2) = wv s.mem B eA (wa + wb + 2) + wv s.mem B ea wa * wv s.mem B eb wb ∧
      Outside B eA (8 * (wa + wb + 2)) s.mem t.mem ∧ Keep mrRegs s t := by
  have hn := hs.nowrap
  unfold mulRows
  refine WP.mono (wp_countdown (N := wa) (by omega) (by omega) (MRInv s B Z ea eb eA wa wb)
    (fun i hi t hI _ => mrStep_ok hs h9 h12 h7 hwb hw hA ha hb sa sb h0 hi hI)
    ⟨hs, Keep.refl _ _, by rw [h11]; simp, by rw [h8]; simp, Outside.refl _ _ _ _, by simp [wv]⟩ h13)
    fun t hI => ⟨by rw [hI.val, Nat.mul_comm], hI.out, hI.keep⟩

end VG.Proof.Bignum.AArch64
