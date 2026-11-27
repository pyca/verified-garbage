module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacState
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacDbls
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
public import VerifiedGarbage.Proof.Weierstrass.Booth
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Weierstrass.Comb
import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Weierstrass.OddWin`, which this module and modules that import it used -/

section

/-!
# Odd 5-bit windows: why no addition is exceptional, on any target

The regular recoding of an odd scalar `k` into `J` odd digits
`d_j = 2 e_j - 31 ∈ [-31, 31]`, `k = Σ_{j<J} d_j 32^j`: `e_j` is window `j`
of `q = (k + 32^J - 1) / 2` (`oq`, `oe`), which the code reads as the 5-bit
windows of `k + 32^J - 1` from its bit 1. With no zero digit, the window
method adds every digit's point, `[|d_j|]P` from a table of odd multiples
reflected for `d_j < 0` (`oddPt`), and needs no mask for a zero digit or an
accumulator `O`.

The accumulator before digit `j` is `[32 S_{j+1}]P`, `S_j = Σ_{i ≥ j} d_i 32^(i-j)`
(`oS`; `S_j = 32 S_{j+1} + d_j`, `oS_step`, and `S_0 = k`, `oS_zero`). Every
`S_j` with `j < J` is odd, so at least 1, and `32^j S_j < k + 32^j`
(`oS_mul`), so the accumulator is never `O` and its sum with the digit's
point is not either (`S_j < n`). The operands are equal only if
`n ∣ 32 S_{j+1} - d_j`, which lies in `(0, n)` for `j ≥ 1`; for `j = 0` it is
`k - 2 d_0 < n + 62`, `n` itself only if `n mod 64 ≥ 33` (`loop_noexc`),
which P-256's `n mod 64 = 17` is not. The top digit is 1 for
`k ≤ 2 · 32^(J-1)` (`oe_top`), so the accumulator starts as `P`.

The table's sums `[2m - 1]P + [2]P` for `1 ≤ m ≤ 15` are not exceptional for
`n > 33` (`tbl_noexc`). An even `k` is replaced by `n - k` (`oddK`), which
for a point killed by `n` (`KilledByN`) gives the opposite point
(`mul_oddK`), of the same `x`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.OddWin

open Spec.Weierstrass

variable {C : Curve}

/-! ## The recoding -/

/-- The recoded scalar, `(k + 32^J - 1) / 2`, whose 5-bit windows are the digits' `e_j`. -/
def oq (J k : Nat) : Nat := (k + (32 ^ J - 1)) / 2

/-- Window `j` of the recoded scalar: the digit `2 e_j - 31`. -/
def oe (J k j : Nat) : Nat := oq J k / 32 ^ j % 32

/-- The digits from `j` up, `Σ_{i ≥ j} d_i 32^(i-j)`. -/
def oS (J k j : Nat) : Nat := 2 * (oq J k / 32 ^ j) + 1 - 32 ^ (J - j)

/-- The point of digit `j`: `[2 e_j - 31]P`, as `[31 - 2 e_j]P` reflected for `e_j < 16`. -/
def oddPt (C : Curve) (P : Point C) (J k j : Nat) : Point C :=
  if 16 ≤ oe J k j then mul (2 * oe J k j - 31) P else negPt (mul (31 - 2 * oe J k j) P)

theorem oe_lt (J k j : Nat) : oe J k j < 32 := Nat.mod_lt _ (by decide)

/-- `2 q = k + 32^J - 1` for odd `k`. -/
theorem two_oq {J k : Nat} (hk : k % 2 = 1) (hJ : 1 ≤ J) : 2 * oq J k = k + 32 ^ J - 1 := by
  have hp : 0 < 32 ^ J := Nat.pow_pos (by decide)
  have he : (k + (32 ^ J - 1)) % 2 = 0 := by
    obtain ⟨J, rfl⟩ : ∃ i, J = i + 1 := ⟨J - 1, by omega_arith⟩
    have : 32 ^ (J + 1) % 2 = 0 := by rw [Nat.pow_succ, Nat.mul_mod]; simp
    omega_arith
  unfold oq; omega_arith

/-- The power `32^(J - j)`'s multiple: `32^J = 32^j 32^(J - j)`. -/
theorem pow_split {J j : Nat} (hj : j ≤ J) : 32 ^ J = 32 ^ j * 32 ^ (J - j) := by
  rw [← Nat.pow_add, Nat.add_sub_cancel' hj]

/-- The subtraction in `oS` is exact. -/
theorem oS_valid {J k j : Nat} (hk : k % 2 = 1) (hJ : 1 ≤ J) (hj : j ≤ J) :
    32 ^ (J - j) ≤ 2 * (oq J k / 32 ^ j) + 1 := by
  have h2 := two_oq (J := J) hk hJ
  have hp : 0 < 32 ^ j := Nat.pow_pos (by decide)
  have hd := Nat.div_add_mod (oq J k) (32 ^ j)
  have hr := Nat.mod_lt (oq J k) hp
  have hs := pow_split hj
  generalize oq J k / 32 ^ j = Q at hd ⊢
  generalize oq J k % 32 ^ j = r at hd hr
  generalize oq J k = q at h2 hd
  rw [hs] at h2
  generalize 32 ^ (J - j) = M at h2 ⊢
  generalize 32 ^ j = a at hp hd hr h2
  refine Nat.le_of_not_lt fun h => ?_
  have hle : a * (2 * Q + 2) ≤ a * M := Nat.mul_le_mul_left a (by omega_arith)
  rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm a 2, Nat.mul_assoc] at hle
  omega_arith

/-- `32^j S_j + 2 (q mod 32^j) + 1 = k + 32^j`. -/
theorem oS_mul {J k j : Nat} (hk : k % 2 = 1) (hJ : 1 ≤ J) (hj : j ≤ J) :
    32 ^ j * oS J k j + 2 * (oq J k % 32 ^ j) + 1 = k + 32 ^ j := by
  have hv := oS_valid (J := J) (j := j) hk hJ hj
  have h2 := two_oq (J := J) hk hJ
  have hd := Nat.div_add_mod (oq J k) (32 ^ j)
  have hs := pow_split hj
  have hp : 0 < 32 ^ j := Nat.pow_pos (by decide)
  unfold oS
  generalize oq J k / 32 ^ j = Q at hd hv ⊢
  generalize oq J k % 32 ^ j = r at hd ⊢
  generalize oq J k = q at h2 hd
  rw [hs] at h2
  generalize 32 ^ (J - j) = M at h2 hv ⊢
  generalize 32 ^ j = a at hp hd h2 ⊢
  have e : a * (2 * Q + 1 - M) + a * M = a * (2 * Q) + a := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hv, Nat.mul_add, Nat.mul_one]
  rw [Nat.mul_left_comm a 2 Q] at e
  omega_arith

/-- `S_0 = k`. -/
theorem oS_zero {J k : Nat} (hk : k % 2 = 1) (hJ : 1 ≤ J) : oS J k 0 = k := by
  have := oS_mul (J := J) (j := 0) hk hJ (Nat.zero_le _)
  simp only [Nat.pow_zero, Nat.mod_one, Nat.one_mul] at this
  omega_arith

/-- `S_j = 32 S_{j+1} + d_j`, with `d_j = 2 e_j - 31`. -/
theorem oS_step {J k j : Nat} (hk : k % 2 = 1) (hj : j < J) :
    oS J k j + 31 = 32 * oS J k (j + 1) + 2 * oe J k j := by
  have hv := oS_valid (J := J) (j := j) hk (by omega_arith) (Nat.le_of_lt hj)
  have hv' := oS_valid (J := J) (j := j + 1) hk (by omega_arith) hj
  have hq : oq J k / 32 ^ j = 32 * (oq J k / 32 ^ (j + 1)) + oe J k j := by
    rw [oe, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod (oq J k / 32 ^ j) 32
    omega_arith
  have hM : 32 ^ (J - j) = 32 * 32 ^ (J - (j + 1)) := by
    rw [show J - j = J - (j + 1) + 1 by omega_arith, Nat.pow_succ, Nat.mul_comm]
  unfold oS
  rw [hq, hM] at hv ⊢
  omega_arith

theorem oS_odd {J k j : Nat} (hk : k % 2 = 1) (hj : j < J) : oS J k j % 2 = 1 := by
  have := oS_step hk hj
  omega_arith

theorem oS_pos {J k j : Nat} (hk : k % 2 = 1) (hj : j < J) : 1 ≤ oS J k j := by
  have := oS_odd hk hj
  omega_arith

/-- `S_j ≤ k / 32^j + 1`. -/
theorem oS_le {J k j : Nat} (hk : k % 2 = 1) (hJ : 1 ≤ J) (hj : j ≤ J) :
    oS J k j ≤ k / 32 ^ j + 1 := by
  have h := oS_mul hk hJ hj
  have hp : 0 < 32 ^ j := Nat.pow_pos (by decide)
  have h1 : oS J k j * 32 ^ j ≤ k + 32 ^ j := by rw [Nat.mul_comm]; omega_arith
  have h2 : oS J k j ≤ (k + 32 ^ j) / 32 ^ j := (Nat.le_div_iff_mul_le hp).mpr h1
  rwa [Nat.add_div_right _ hp] at h2

/-- For `j ≥ 1`, `S_j ≤ k / 32 + 1`. -/
theorem oS_le_32 {J k j : Nat} (hk : k % 2 = 1) (hj : j ≤ J) (h1 : 1 ≤ j) : oS J k j ≤ k / 32 + 1 := by
  have := oS_le hk (by omega_arith) hj
  have : k / 32 ^ j ≤ k / 32 := Nat.div_le_div_left (by
    calc 32 = 32 ^ 1 := rfl
      _ ≤ 32 ^ j := Nat.pow_le_pow_right (by decide) h1) (by decide)
  omega_arith

/-- The top window is 16, its digit 1, for `k ≤ 2 · 32^(J-1)`. -/
theorem oe_top {J k : Nat} (hk : k % 2 = 1) (hJ : 1 ≤ J) (hkb : k ≤ 2 * 32 ^ (J - 1)) :
    oe J k (J - 1) = 16 ∧ oS J k (J - 1) = 1 := by
  have h2 := two_oq (J := J) hk hJ
  have hs : 32 ^ J = 32 * 32 ^ (J - 1) := by
    rw [show J = J - 1 + 1 by omega_arith, Nat.pow_succ, Nat.add_sub_cancel, Nat.mul_comm]
  have hp : 0 < 32 ^ (J - 1) := Nat.pow_pos (by decide)
  have hQ : oq J k / 32 ^ (J - 1) = 16 := by
    rw [Nat.div_eq_iff hp]
    constructor <;> rw [hs] at h2 <;> omega_arith
  refine ⟨by rw [oe, hQ], ?_⟩
  unfold oS
  rw [hQ, show J - (J - 1) = 1 by omega_arith]

/-! ## Points -/

/-- The digit's point as an integer multiple. -/
theorem oddPt_zmul (P : Point C) (J k j : Nat) :
    oddPt C P J k j = zmul (2 * (oe J k j : Int) - 31) P := by
  unfold oddPt zmul
  by_cases h : 16 ≤ oe J k j
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith))]
    congr 1; omega_arith
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]
    congr 2; omega_arith

theorem onCurve_oddPt (hC : Law C) {P : Point C} (hP : onCurve C P = true) (J k j : Nat) :
    onCurve C (oddPt C P J k j) = true := by
  unfold oddPt
  split
  · exact hC.onCurve_mul hP _
  · exact onCurve_negPt (hC.onCurve_mul hP _)

/-- An iteration's addition: `[32 S_{j+1}]P + [d_j]P = [S_j]P`. -/
theorem win_add (hC : Law C) {P : Point C} (hP : onCurve C P = true) {J k j : Nat}
    (hk : k % 2 = 1) (hj : j < J) :
    Spec.Weierstrass.add (mul (32 * oS J k (j + 1)) P) (oddPt C P J k j) = mul (oS J k j) P := by
  have hs := oS_step hk hj
  have hpos := oS_pos hk hj
  unfold oddPt
  split
  · rw [hC.add_mul_mul hP]; congr 1; omega_arith
  · rw [hC.add_mul_neg hP (by omega_arith)]; congr 1; omega_arith

/-! ## No exceptional addition -/

/-- A positive multiple of `n` below `2 n` is `n`. -/
theorem eq_of_dvd_lt {n : Nat} {x : Int} (h : (n : Int) ∣ x) (h0 : 0 < x) (h2 : x < 2 * n) : x = n := by
  obtain ⟨c, rfl⟩ := h
  rcases Int.lt_or_le c 1 with h1 | h1
  · have : (n : Int) * c ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega_arith) (by omega_arith)
    omega_arith
  · rcases Int.lt_or_le c 2 with h3 | h3
    · have : c = 1 := by omega_arith
      subst this; omega_arith
    · have : (n : Int) * 2 ≤ n * c := Int.mul_le_mul_of_nonneg_left h3 (by omega_arith)
      omega_arith

/-- The loop's addition of digit `j`'s point to `[32 S_{j+1}]P`, `j + 1 < J`:
the accumulator is not `O`, and the points differ and are not opposite. -/
theorem loop_noexc (hC : Law C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33) (hnb : 128 ≤ C.n)
    {J k j : Nat} (hk : k % 2 = 1) (hkn : k < C.n) (hj : j + 1 < J) :
    mul (32 * oS J k (j + 1)) P ≠ .infinity ∧ mul (32 * oS J k (j + 1)) P ≠ oddPt C P J k j ∧
      Spec.Weierstrass.add (mul (32 * oS J k (j + 1)) P) (oddPt C P J k j) ≠ .infinity := by
  have hs := oS_step (J := J) (j := j) hk (by omega_arith)
  have h1 := oS_pos (J := J) (j := j + 1) hk hj
  have h0 := oS_pos (J := J) (j := j) hk (by omega_arith)
  have he := oe_lt J k j
  -- `S_j < n`, and `S_j ≤ k / 32 + 1` for `j ≥ 1`.
  have hS : oS J k j < C.n ∧ (1 ≤ j → oS J k j ≤ k / 32 + 1) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [oS_zero (J := J) hk (by omega_arith)]; exact ⟨hkn, fun h => absurd h (by decide)⟩
    · have := oS_le_32 (J := J) hk (j := j) (by omega_arith) hj1
      exact ⟨by omega_arith, fun _ => this⟩
  have hadd := win_add hC hP (J := J) (j := j) hk (by omega_arith)
  generalize oS J k (j + 1) = s1 at hs h1 hadd ⊢
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hd := hO P hP hP0 _ h
    have := eq_of_dvd_lt (n := C.n) (x := ((32 * s1 : Nat) : Int)) (Int.natCast_dvd_natCast.mpr hd)
      (by omega_arith) (by omega_arith)
    omega_arith
  · rw [oddPt_zmul, ← zmul_natCast] at h
    have hd := Window5.zmul_dvd hC hO hP hP0 h
    have := eq_of_dvd_lt hd (by omega_arith) (by omega_arith)
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · -- `k - 2 d_0 = n` makes `n mod 64 = 63 - 2 e_0 ≥ 33`.
      rw [oS_zero (J := J) hk (by omega_arith)] at hs
      have h2 := two_oq (J := J) hk (by omega_arith)
      have hq := Nat.div_add_mod (oq J k) 32
      have hp : 32 ^ J = 64 * (32 ^ (J - 2) * 16) := by
        rw [show J = J - 2 + 2 by omega_arith, Nat.pow_add, Nat.add_sub_cancel]; omega_arith
      have : oe J k 0 = oq J k % 32 := by simp [oe]
      omega_arith
    · have := hS.2 hj1
      omega_arith
  · rw [hadd] at h
    exact Window5.mul_ne_infinity hO hP hP0 h0 hS.1 h

/-- The table's co-Z addition `[2m - 1]P + [2]P`, `1 ≤ m ≤ 15`, for `n > 33`: the
points differ and are not opposite. -/
theorem tbl_noexc (hC : Law C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn : 34 ≤ C.n) {m : Nat} (h1 : 1 ≤ m) (h15 : m ≤ 15) :
    mul (2 * m - 1) P ≠ mul 2 P ∧
      Spec.Weierstrass.add (mul (2 * m - 1) P) (mul 2 P) ≠ .infinity := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : zmul ((2 : Nat) : Int) P = zmul ((2 * m - 1 : Nat) : Int) P := by
      rw [zmul_natCast, zmul_natCast, h]
    have hd := Window5.zmul_dvd hC hO hP hP0 h'
    have hd' : (C.n : Int) ∣ ((2 * m - 1 : Nat) : Int) - (2 : Nat) := by
      rw [← Int.neg_sub]; exact Int.dvd_neg.mpr hd
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have : m = 1 := by omega_arith
      subst this
      exact Window5.not_dvd_of_pos_lt (n := C.n) (x := (2 : Nat) - ((2 * 1 - 1 : Nat) : Int))
        (by omega_arith) (by omega_arith) hd
    · exact Window5.not_dvd_of_pos_lt (n := C.n) (x := ((2 * m - 1 : Nat) : Int) - (2 : Nat))
        (by omega_arith) (by omega_arith) hd'
  · rw [hC.add_mul_mul hP] at h
    exact Window5.mul_ne_infinity hO hP hP0 (m := 2 * m - 1 + 2) (by omega_arith) (by omega_arith) h

/-! ## Odd scalars -/

/-- The odd scalar for `d`: `d` if odd, else `n - d`. -/
def oddK (n d : Nat) : Nat := if d % 2 = 1 then d else n - d

theorem oddK_odd {n d : Nat} (hn : n % 2 = 1) (hd : d ≤ n) : oddK n d % 2 = 1 := by
  unfold oddK; split <;> omega_arith

theorem oddK_lt {n d : Nat} (hd1 : 1 ≤ d) (hdn : d < n) : 1 ≤ oddK n d ∧ oddK n d < n := by
  unfold oddK; split <;> omega_arith

/-- `[n - d]P = -[d]P` for a point killed by `n`, so `oddK` gives `±[d]P`. -/
theorem mul_oddK (hC : Law C) {P : Point C} (hP : onCurve C P = true) (hK : mul C.n P = .infinity)
    {d : Nat} (hd1 : 1 ≤ d) (hd : d ≤ C.n) :
    mul (oddK C.n d) P = if d % 2 = 1 then mul d P else negPt (mul d P) := by
  unfold oddK
  split
  · rfl
  · have e := hC.add_zmul hP (C.n : Int) (-(d : Int))
    rw [zmul_natCast, hK, infinity_add', show (C.n : Int) + -(d : Int) = ((C.n - d : Nat) : Int) by omega_arith,
      zmul_natCast] at e
    rw [← e, zmul, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]
    congr 2; omega_arith

end VG.Proof.Weierstrass.OddWin

end

end

/-!
# The odd window method on x86-64: what holds between its steps

As `WinJacState.lean`, for the table of odd multiples: entries `1 … M` hold
`[2m - 1]P` (`JTblOkO`); what the method reads at the start, the table of
bits that of `oq J k` (`JacWinFixedO`); and between doublings, the frame,
the table and `R` (`RStO`, `dblsO_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- Entries `1 … M` of the table hold `[2m - 1]P`. -/
def JTblOkO (K : JacWinCfg) (C : Curve) (base : Addr) (P : Point C) (M : Nat) (s : State) : Prop :=
  ∀ m, 1 ≤ m → m ≤ M → JPt C K.M.n base s (entS K m) (mul (2 * m - 1) P)

variable {K : JacWinCfg} {size : Nat} {C : Curve}

theorem JTblOkO.unch (hL : JacWinLay K size) {base : Addr} {P : Point C} {M : Nat}
    {s s' : State} (hT : JTblOkO K C base P M s) {W : List (Nat × Nat)} (hU : Unch base W s.mem s'.mem)
    (hn : base.toNat + size ≤ 2 ^ 64) (hM : M ≤ 16)
    (hW : ∀ w ∈ W, ∀ i < 5 * M, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i) :
    JTblOkO K C base P M s' := fun m h1 hm =>
  (hT m h1 hm).congr fun c hc => jgWord_unch hL hU hn (by omega_using [hM, hm, hc]) fun w hw => hW w hw _ (by omega_using [h1, hm, hc])

/-- A program's writes keep entries `1 … M` if the loop may write them. -/
theorem JTblOkO.loopW (hL : JacWinLay K size) {base : Addr} {P : Point C} {M : Nat} {s s' : State}
    (hT : JTblOkO K C base P M s) (hU : Unch base (jwLoopW K) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64)
    (hM : M ≤ 16) : JTblOkO K C base P M s' :=
  hT.unch hL hU hn hM fun w hw i hi => loopW_apart hL (by omega_using [hM, hi]) w hw

/-- Storing entry `M + 1` keeps entries `1 … M`. -/
theorem JTblOkO.store (hL : JacWinLay K size) {base : Addr} {P : Point C} {M : Nat} {s s' : State}
    (hT : JTblOkO K C base P M s)
    (hO : Outside base (jg K (5 * M)) (40 * K.M.n) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64)
    (hM : M ≤ 15) : JTblOkO K C base P M s' :=
  hT.unch hL (outside_grid5 hO) hn (by omega_using [hM]) fun w hw i hi => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
    refine jg_sep K ?_; omega_using [hi]

/-- What the odd method reads and never writes, at the start: zero, `P`, and
the table of the bits of `oq J k = (k + 32^J - 1) / 2`. -/
structure JacWinFixedO (K : JacWinCfg) (C : Curve) (base : Addr) (s₀ : State) (P : Point C) (k : Nat) :
    Prop extends JacWinPt K C base s₀ P where
  bits : ∀ t < 5 * K.J, s₀.mem (off base (K.bits + t)) =
    if (OddWin.oq K.J k).testBit t then 1 else 0

/-- `P ≠ O`: its `Z` is one. -/
theorem JacWinFixedO.ne_infinity (hC : Law C) {base : Addr} {s₀ : State} {P : Point C} {k : Nat}
    (hF : JacWinFixedO K C base s₀ P k) : P ≠ .infinity := by
  intro h
  have := hF.pt
  rw [h, hF.pz] at this
  exact hC.one_ne_zero this.2.2

/-- What holds between doublings: the frame, the odd table, and `R` a
Jacobian triple of `Q`. -/
structure RStO (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (Q : Point C) (s : State) : Prop where
  fr : JFrame K C base size s₀ s
  tbl : JTblOkO K C base P 16 s
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  rep : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) Q

theorem RStO.rbxKeeps (hL : JacWinLay K size) {base : Addr} {P Q : Point C} {s₀ s s' : State}
    (h : RStO K C base size P s₀ Q s) (hk : Keeps [.rbx] s s') : RStO K C base size P s₀ Q s' := by
  have m : s'.mem = s.mem := hk.2.1
  have e : ∀ x, tmv C K.M.n base s' x = tmv C K.M.n base s x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [m]
  refine ⟨h.fr.next hL (h.fr.scr.of_keeps hk (by decide)) ((Keeps.regs hk).mono (sub_powClob (by decide)))
    (W := []) (by rw [m]; exact Unch.refl _ _ _) (by simp), fun j h1 hj => (h.tbl j h1 hj).congr
    fun c _ => by rw [m], fun x hx => by rw [m]; exact h.lt x hx, by rw [e, e, e]; exact h.rep⟩

/-- What the loop's doublings write: the other slots and the temporary area,
not the grid. -/
def jwOthW (K : JacWinCfg) : List (Nat × Nat) := (jwOther K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)]

theorem jwOthW_loopW (K : JacWinCfg) : ∀ w ∈ jwOthW K, w ∈ jwLoopW K := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw; exact other_loopW hx
  · rw [List.mem_singleton.mp hw]; exact tmp_loopW

/-- One doubling of `R`. -/
theorem dblRO_ok (hL : JacWinLay K size) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    {base : Addr} {P Q : Point C} (hQ : onCurve C Q = true) {s₀ s : State}
    (h : RStO K C base size P s₀ Q s) :
    WP isa (dbl K.R).inline s fun t => RStO K C base size P s₀ (Spec.Weierstrass.add Q Q) t ∧
      t.gpr .rbx = s.gpr .rbx ∧ Unch base (jwOthW K) s.mem t.mem := by
  have hs := h.fr.scr
  have hn := hs.nowrap
  have hRo : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ jwOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  have I0 : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z] (tmv C K.M.n base s) s :=
    ⟨hs, h.fr.mod, fun x hx => other_mem (hRo x hx), h.lt, fun _ _ => rfl⟩
  have hsl : ∀ x ∈ rcbW K.S K.R, x ∈ jwSlots K := by
    intro x hx
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jw_mem
  refine WP.mono (hD hL.lay hL.rcbW_R hsl I0 hQ h.rep) fun t ⟨k, E, I, J⟩ => ?_
  have hRw : ∀ x ∈ rcbW K.S K.R, x ∈ jwOther K := by
    intro x hx
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jw_mem
  have U' : Unch base (jwOthW K) s.mem t.mem := (ProgKeep.unch k).mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_map_of_mem (hRw x hx))
    · exact List.mem_append_right _ hw
  have U : Unch base (jwLoopW K) s.mem t.mem := U'.mono (jwOthW_loopW K)
  refine ⟨⟨h.fr.next hL (k.scr hs) k.regs U (jwLoopW_sub K), h.tbl.loopW hL U hn (by decide),
    fun x hx => I.lt x hx, ?_⟩, k.gpr _ (rbx_not_clob _), U'⟩
  have e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base t x = E x := fun x hx => I.val x hx
  rw [e _ (by simp), e _ (by simp), e _ (by simp)]
  exact J

/-- `R = 32 R`, `rbx` the window index `j < 4096` before and after. -/
theorem dblsO_ok (hL : JacWinLay K size) (hC : Law C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    {base : Addr} {P Q : Point C} (hQ : onCurve C Q = true) {s₀ s : State} {e j : Nat} (hj : j < 4096)
    (hb : s.gpr .rbx = BitVec.ofNat 64 j) (h : RStO K C base size P s₀ (mul e Q) s) :
    WP isa (K.dbls dbl).inline s fun t => RStO K C base size P s₀ (mul (32 * e) Q) t ∧
      t.gpr .rbx = BitVec.ofNat 64 j ∧ Unch base (jwOthW K) s.mem t.mem := by
  rw [JacWinCfg.dbls]
  simp only [Code.inline]
  refine WP.seq (WP.mono (addRbx_ok s (c := 5 * 4096) (by decide) hb) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  refine aeLoop_ok (n := 5) (Inv := fun i t => RStO K C base size P s₀ (mul (2 ^ (5 - i) * e) Q) t ∧
      t.gpr .rbx = BitVec.ofNat 64 (j + 4096 * i) ∧ Unch base (jwOthW K) s.mem t.mem)
    (fun i t h1 h5 ⟨R, b, U⟩ => ?_) (fun t ⟨R, b, U⟩ => ⟨by simpa using R, by simpa using b, U⟩) (by decide)
    ⟨by simpa using h.rbxKeeps hL k₁, by rw [b₁], by rw [m₁]; exact Unch.refl _ _ _⟩
  rw [JacWinCfg.dblStep]
  refine WP.seq (WP.mono (dblRO_ok hL hD (hC.onCurve_mul hQ _) R) fun t₁ ⟨R₁, b₁', U₁⟩ => ?_)
  refine WP.mono (dblCount_ok t₁ hj h1 h5 (by rw [b₁', b])) fun t₂ ⟨b₂, c₂, k₂⟩ =>
    ⟨⟨?_, b₂, by rw [k₂.2.1]; exact (U.trans U₁).mono fun w hw => (List.mem_append.mp hw).elim id id⟩, c₂⟩
  have := R₁.rbxKeeps hL k₂
  rwa [hC.add_mul_mul hQ, show 2 ^ (5 - i) * e + 2 ^ (5 - i) * e = 2 ^ (5 - (i - 1)) * e by
    rw [show 5 - (i - 1) = 5 - i + 1 by omega_using [h1, h5], Nat.pow_succ]; grind] at this

end VG.Proof.Weierstrass.X86_64
