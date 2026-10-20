module

public import VerifiedGarbage.Proof.Rsa.X86.RvWindowTable
public import VerifiedGarbage.Proof.Rsa.X86.RvCount
public import VerifiedGarbage.Proof.Rsa.X86.RvMont
import VerifiedGarbage.Proof.Bignum.Math

/-! # The candidate's power, one 4-bit window of the exponent per iteration

After `i` windows of the (aligned) exponent `E` of `L` bits, the exponent's
words hold `E 16^i mod 2^L` and `mY` the candidate's power to the top
`4 i` bits, `E 16^i / 2^L`, in Montgomery form.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic (window_exponent window_power)

abbrev liveWin : List Nat := List.range 16 ++ liveExp

/-- The windowed exponentiation after `i` of its `C` windows. -/
def WI (g : Geo) (s0 : State) (T AW V : Nat → Nat) (m b E C i : Nat) (s : State) : Prop :=
  KS g s0 (upd T mY (b ^ (E * 16 ^ i / 2 ^ (32 * g.W)) * 2 ^ (64 * g.n) % m)) liveWin
    (upd AW wRc (E * 16 ^ i % 2 ^ (32 * g.W))) [wRc, wR] (upd V sCnt (C - i)) slotsExp s

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {V : Nat → Nat} {ls : List Nat} {m : Nat}

/-- `mY` times the array `b`, in Montgomery form. -/
theorem KS.mulY {b y z : Nat} (h : KS g s0 A live AW [wRc, wR] V ls s)
    (hY : mY ∈ live) (hb : b ∈ live) (hB : mBase ∈ live) (hI : sInv ∈ ls) (value : A mBase = m)
    (bound : m < 2 ^ (64 * g.n)) (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1)
    (positive : 0 < m) (hl : ∀ j ∈ live, j ≠ mTmp ∧ j ≠ mAcc ∧ j ≠ mAcc + 1)
    (index : MontIndex b)
    (hy : A mY = y * 2 ^ (64 * g.n) % m) (hz : A b = z * 2 ^ (64 * g.n) % m) :
    WP isa (VG.Impl.Rsa.X86.Recover.mmul g.n mY mY b) s fun t =>
      KS g s0 (upd A mY (y * z * 2 ^ (64 * g.n) % m)) live AW [wRc, wR] V ls t := by
  have mr := h.montReady hB hI value bound inverse
  refine WP.mono (h.mmul mr (o := mY) (a := mY) (b := b) (by decide) (by decide) index
    (by decide) hY hb (by rw [hy]; exact Nat.mod_lt _ positive) (by rw [hz]; exact Nat.mod_lt _ positive)
    (fun j hj => .inr (hl j hj)) (by decide)) fun t ⟨X, ht, _, _, lt, v⟩ => ?_
  have p := VG.Proof.Dsa.mont_product (VG.Proof.Bignum.coprime_pow2 odd _) (a := y) (b := z)
    (by rw [hy, Nat.mod_mod]) (by rw [hz, Nat.mod_mod]) v
  rw [Nat.mod_eq_of_lt lt] at p
  rw [p] at ht
  exact ht.mono (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun d hd => ⟨hd, rfl⟩)

theorem KS.squareY {y : Nat} (h : KS g s0 A live AW [wRc, wR] V ls s)
    (hY : mY ∈ live) (hB : mBase ∈ live) (hI : sInv ∈ ls) (value : A mBase = m)
    (bound : m < 2 ^ (64 * g.n)) (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1)
    (positive : 0 < m) (hl : ∀ j ∈ live, j ≠ mTmp ∧ j ≠ mAcc ∧ j ≠ mAcc + 1)
    (hy : A mY = y * 2 ^ (64 * g.n) % m) :
    WP isa (VG.Impl.Rsa.X86.Recover.square g.n) s fun t =>
      KS g s0 (upd A mY (y ^ 2 * 2 ^ (64 * g.n) % m)) live AW [wRc, wR] V ls t := by
  refine WP.mono (h.mulY hY hY hB hI value bound inverse odd positive hl (by decide) hy hy)
    fun t ht => ?_
  rwa [← Nat.pow_two] at ht

end

theorem liveWin_apart : ∀ j ∈ liveWin, j ≠ mTmp ∧ j ≠ mAcc ∧ j ≠ mAcc + 1 := by decide

theorem windowBody_ok {g : Geo} {s0 s : State} {T AW V : Nat → Nat} {m b E C i : Nat}
    (h : WI g s0 T AW V m b E C i s)
    (table : ∀ j < 16, T j = b ^ j * 2 ^ (64 * g.n) % m)
    (value : T mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1) (positive : 0 < m)
    (hi : i < C) (hC : C < 2 ^ 32) :
    WP isa (windowBody g.n) s fun t =>
      WI g s0 T AW V m b E C (i + 1) t ∧ t.zf = some (decide (C - (i + 1) = 0)) := by
  have hP : 0 < 2 ^ (32 * g.W) := Nat.two_pow_pos _
  have vbase : ∀ y, upd T mY y mBase = m := fun y => by rw [upd_ne _ _ (by decide)]; exact value
  have vinv : (m * upd V sCnt (C - i) sInv + 1) % 2 ^ 32 = 0 := by
    rw [upd_ne _ _ (by decide)]; exact inverse
  unfold windowBody
  simp only [seqs]
  unfold WI at h
  refine WP.seq (WP.mono (h.squareY (by decide) (by decide) (by decide) (vbase _) bound vinv odd positive
    liveWin_apart (upd_self _ _ _)) fun s1 h1 => ?_)
  simp only [upd_twice] at h1
  refine WP.seq (WP.mono (h1.squareY (by decide) (by decide) (by decide) (vbase _) bound vinv odd positive
    liveWin_apart (upd_self _ _ _)) fun s2 h2 => ?_)
  simp only [upd_twice] at h2
  refine WP.seq (WP.mono (h2.squareY (by decide) (by decide) (by decide) (vbase _) bound vinv odd positive
    liveWin_apart (upd_self _ _ _)) fun s3 h3 => ?_)
  simp only [upd_twice] at h3
  refine WP.seq (WP.mono (h3.squareY (by decide) (by decide) (by decide) (vbase _) bound vinv odd positive
    liveWin_apart (upd_self _ _ _)) fun s4 h4 => ?_)
  simp only [upd_twice] at h4
  -- The window, and the exponent shifted past it.
  refine WP.seq (WP.mono (h4.windowTop_ok (by decide)) fun s5 ⟨h5, _⟩ => ?_)
  rw [upd_self] at h5
  refine WP.seq (WP.mono (h5.shiftUp_W (j := wRc) (by simp) (by decide)) fun s6 ⟨h6, _⟩ => ?_)
  rw [upd_self, upd_twice] at h6
  have small : E * 16 ^ i % 2 ^ (32 * g.W) * 16 / 2 ^ (32 * g.W) < 16 := by
    rw [Nat.div_lt_iff_lt_mul hP]
    have := Nat.mod_lt (E * 16 ^ i) hP
    omega
  have h6' := h6.mono (liveW' := [wRc, wR]) (fun j hj => ⟨hj, rfl⟩)
    (fun j hj => ⟨by simp [hj], rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.seq (WP.mono (scan_ok h6' (by intro j hj; simp [List.mem_range]; omega) (by simp)
    (by rw [upd_self]; exact small) (by decide) 15 (by decide)) fun s7 h7 => ?_)
  simp only [upd_self, show E * 16 ^ i % 2 ^ (32 * g.W) * 16 / 2 ^ (32 * g.W) ≤ 15 by omega,
    ↓reduceIte] at h7
  have entry : upd T mY (((((b ^ (E * 16 ^ i / 2 ^ (32 * g.W))) ^ 2) ^ 2) ^ 2) ^ 2 * 2 ^ (64 * g.n) % m)
      (E * 16 ^ i % 2 ^ (32 * g.W) * 16 / 2 ^ (32 * g.W)) =
      b ^ (E * 16 ^ i % 2 ^ (32 * g.W) * 16 / 2 ^ (32 * g.W)) * 2 ^ (64 * g.n) % m := by
    rw [upd_ne _ _ (by unfold mY; omega)]
    exact table _ small
  refine WP.seq (WP.mono (h7.mulY (b := mXm) (by decide) (by decide) (by decide) (by decide)
    (by rw [upd_ne _ _ (by decide)]; exact vbase _) bound
    (by rw [upd_ne _ _ (by decide)]; exact vinv) odd positive (by decide) (by decide)
    (by rw [upd_ne _ _ (by decide), upd_self]) (by rw [upd_self]; exact entry)) fun s8 h8 => ?_)
  have count : upd (upd V sCnt (C - i)) sWin (E * 16 ^ i % 2 ^ (32 * g.W) * 16 / 2 ^ (32 * g.W)) sCnt =
      C - i := by
    rw [upd_ne _ _ (by decide), upd_self]
  refine WP.mono (h8.cntNext_ok (by simp) (by rw [count]; omega) (by rw [count]; omega))
    fun t ⟨ht, zt⟩ => ⟨?_, ?_⟩
  · unfold WI
    refine ht.mono (fun j hj => ⟨by simp [hj], ?_⟩) (fun j hj => ⟨hj, ?_⟩)
      (fun d hd => ⟨by simp [hd], ?_⟩)
    · by_cases e : j = mY
      · subst e
        rw [upd_self, upd_self]
        congr 2
        rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, window_power, Nat.pow_succ,
          ← Nat.mul_assoc, window_exponent (E * 16 ^ i) _ hP]
      · have nx : j ≠ mXm := by
          intro x; subst x; revert hj; decide
        rw [upd_ne _ _ e, upd_ne _ _ nx, upd_ne _ _ e, upd_ne _ _ e]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · rw [upd_self, upd_self, Nat.pow_succ, ← Nat.mul_assoc, Nat.mod_mul_mod]
      · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]
    · by_cases e : d = sCnt
      · subst e
        rw [upd_self, upd_self, count]
        omega
      · have nw : d ≠ sWin := by
          intro x; subst x; revert hd; decide
        rw [upd_ne _ _ e, upd_ne _ _ nw, upd_ne _ _ e, upd_ne _ _ e]
  · rw [zt, count, Nat.sub_sub]

end VG.Proof.Rsa.X86.Recover
