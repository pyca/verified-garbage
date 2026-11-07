module

public import VerifiedGarbage.Impl.MillerRabin.RISCV64.Search
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Prep
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
public import VerifiedGarbage.Proof.Mont.Words32
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMont
import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.PubSan
import VerifiedGarbage.Proof.Bignum.RISCV64.Double64
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFios
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A prime search on RISC-V: a modulus's Montgomery constants

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Search/MontPrep.lean`):
`montPrepWith_ok`, for an odd `N ≥ 3` in array 0, `−N⁻¹ mod 2⁶⁴` in `t1` and
header word 7, `R² mod N` in array 1, `R mod N` in array 9 (by way of array
6), `N − R mod N` in array 10, and Miller–Rabin's exponent in array 27
(`expSetup_ok`), `R = 2^(64 w)`, given a computation of `R² mod N` and
`−N⁻¹` (`R2Ok`); `montPrepHi_ok` with `Precompute.r2` (`r2Inv_ok`), for `N`
above `2^(64 (w − 1))`.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Search

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.MillerRabin.RISCV64 VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.Bignum.RISCV64
open VG.Proof.MillerRabin.RISCV64 (Env A MCtx expSetup_ok prepRegs copy_ok copyRegs slot_lt)
open VG.Proof.Bignum (slot Arrays)
open VG.Proof.RsaKeyGen (mrE mrA)
open VG.Impl.Bignum.RISCV64.PublicChecked (base montOp)

/-! ## `R² mod N` and `−N⁻¹` -/

/-- `Precompute.r2`, with `−N⁻¹` in `t1`: `r2_ok`, which keeps the inverse
`minv` leaves through the squares. -/
theorem r2Inv_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B (slot w 1)) (h5 : s.gpr .a5 = off B (slot w 2)) (h6 : s.gpr .a6 = off B (slot w 3))
    (h7 : s.gpr .a7 = off B (slot w 0)) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (hN : 2 ^ (64 * (w - 1)) ≤ wordsVal s.mem B (slot w 0) w) (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1) :
    WP isa Impl.Bignum.RISCV64.Precompute.r2 s fun t =>
      (wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
        ((word s.mem B (slot w 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0) ∧
      Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep r2Regs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hlow : (word s.mem B (slot w 0)).toNat % 2 = 1 := by
    rw [fios_wordsVal_pred _ _ _ (show 1 ≤ w by omega)] at hodd
    omega
  generalize hNd : wordsVal s.mem B (slot w 0) w = N at hN hodd ⊢
  replace hN : 2 ^ (64 * (w - 1)) < N := Nat.lt_of_le_of_ne hN fun h => by
    rw [← h, show 64 * (w - 1) = (64 * (w - 1) - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left] at hodd
    exact absurd hodd (by decide)
  have hN0 : 0 < N := by omega
  unfold Impl.Bignum.RISCV64.Precompute.r2
  refine WP.seq (WP.mono (r2HiDbl_ok hs h5 h6 h7 h2 ht0 hw hw' (by omega) hNd hN) fun s₃ ⟨x3, o3, k3⟩ => ?_)
  have n3 : wordsVal s₃.mem B (slot w 0) w = N := by rw [Outside.wordsVal o3 (by omega) (by omega), hNd]
  have w3 : word s₃.mem B (slot w 0) = word s.mem B (slot w 0) := Outside.word o3 (by omega) (by omega)
  refine WP.seq (WP.mono (minv_ok (hs.congr k3.2.2) ((k3.gpr (by decide)).trans h7) (slot_al8 w 0) (by omega)
    (by rw [w3]; exact hlow)) fun s₄ ⟨⟨i4, m4⟩, k4⟩ => ?_)
  have k34 := k3.trans k4
  have i4' : ((word s.mem B (slot w 0)).toNat * (s₄.gpr .t1).toNat + 1) % 2 ^ 64 = 0 := by rw [← w3]; exact i4
  rw [← m4] at x3 n3 w3
  refine WP.mono (r2Squares_ok (N := N) (hs.congr k34.2.2) hw hw' hZ ((k34.gpr (by decide)).trans h2)
    ((k34.gpr (by decide)).trans h5) ((k34.gpr (by decide)).trans h6) ((k34.gpr (by decide)).trans h7)
    ((k34.gpr (by decide)).trans ht0) (by rw [m4]; exact i4) n3 hodd
    (by rw [x3]; exact Nat.mod_lt _ hN0) (by rw [x3, Nat.mod_mod, Nat.pow_add]))
    fun t ⟨tx, to, tk⟩ => ⟨⟨tx, by rw [tk.gpr (by decide)]; exact i4'⟩, Outside.trans (by rw [m4]; exact o3) to,
      (k34.trans tk).mono (by decide)⟩

/-! ## `montPrepWith` -/

/-- What `montPrepWith` changes: header word 7, arrays 1–3, 6–7, 9–10 and 27. -/
def mpRanges (w : Nat) : List (Nat × Nat) :=
  [(56, 8), (slot w 1, 24 * (w + 2)), (slot w 6, 16 * (w + 2)), (slot w 9, 16 * (w + 2)), (slot w aE, 8 * (w + 2))]

/-- The registers `montPrepWith` writes. -/
def mpRegs : List Reg :=
  [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- A computation of `R² mod N` into array 1 for `montPrepWith`, for an odd
`N ≥ 3` in array 0 with `P w N`: from the bases of arrays 1–3 in `a2`, `a5`
and `a6`, `−N⁻¹ mod 2⁶⁴` into `t1`, writing only arrays 1–3 and `r2Regs`. -/
def R2Ok (r2c : Prog isa) (P : Nat → Nat → Prop) : Prop :=
  ∀ {s : State} {B : Addr} {Z w N : Nat}, Env s B Z w → s.gpr .a2 = off B (slot w 1) →
    s.gpr .a5 = off B (slot w 2) → s.gpr .a6 = off B (slot w 3) →
    A s.mem B w 0 = N → N % 2 = 1 → 3 ≤ N → P w N →
    WP isa r2c s fun t => (A t.mem B w 1 = 2 ^ (128 * w) % N ∧
      ((word s.mem B (slot w 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0) ∧
      Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep r2Regs s t

theorem r2_r2Ok : R2Ok Impl.Bignum.RISCV64.Precompute.r2 fun w N => 2 ^ (64 * (w - 1)) < N := by
  intro s B Z w N h h2 h5 h6 hN hodd _ hNt
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  refine WP.mono (r2Inv_ok h.hs h2 h5 h6 h.a7 h.t0 (by omega) (by omega) (by simp only [es] at hZ ⊢; omega)
    (by rw [show wordsVal s.mem B (slot w 0) w = A s.mem B w 0 from rfl, hN]; omega)
    (by rw [show wordsVal s.mem B (slot w 0) w = A s.mem B w 0 from rfl, hN]; exact hodd))
    fun t ⟨⟨r, i⟩, o, k⟩ => ⟨⟨by rw [A, r, show wordsVal s.mem B (slot w 0) w = A s.mem B w 0 from rfl, hN], i⟩, o, k⟩

/-- Ranges cover. -/
theorem outs_of {B : Addr} {w o n : Nat} {m m' : Mem} (h : Outside B o n m m')
    (hr : ∃ R ∈ mpRanges w, R.1 ≤ o ∧ o + n ≤ R.1 + R.2) : Outs B (mpRanges w) m m' :=
  Outs.cover (Outs.of_outside h (List.mem_singleton_self _)) fun r hr' => by
    rw [List.mem_singleton] at hr'; subst hr'; exact hr

/-- `montPrepWith r2c`, for `r2c` computing `R² mod N` and `−N⁻¹` under `P w N`. -/
theorem montPrepWith_ok {r2c : Prog isa} {P : Nat → Nat → Prop} (hr2 : R2Ok r2c P) {s : State} {B : Addr}
    {Z w N : Nat} (h : Env s B Z w) (hn : A s.mem B w 0 = N) (hodd : N % 2 = 1) (hN3 : 3 ≤ N)
    (hP : P w N) :
    WP isa (montPrepWith r2c) s fun t =>
      (Env t B Z w ∧ A t.mem B w 0 = N ∧
        ((word t.mem B (slot w 0)).toNat * (word t.mem B 56).toNat + 1) % 2 ^ 64 = 0 ∧
        ((word t.mem B (slot w 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0 ∧
        A t.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧ A t.mem B w 9 = 2 ^ (64 * w) % N ∧
        A t.mem B w 10 = N - 2 ^ (64 * w) % N ∧ A t.mem B w aE = mrE N ∧
        t.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA N % 64) ∧
        Outs B (mpRanges w) s.mem t.mem) ∧ Keep mpRegs s t := by
  have hnw := h.hs.nowrap
  have hZ := h.hZ
  have hw4 := h.hw
  have hw128 := h.hw'
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ Z := by rw [← es]; exact hZ
  have al := slot_al8 w
  unfold montPrepWith
  -- The arrays' addresses.
  refine WP.seq ?_
  simp only [r2Bases, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .a2) (by decide) 1) fun s₁ ⟨⟨a2, m₁⟩, k₁⟩ => ?_
  have e₁ := h.keep k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e₁.base (rd := .a5) (by decide) 2) fun s₂ ⟨⟨a5, m₂⟩, k₂⟩ => ?_
  have e₂ := e₁.keep k₂ (by decide)
  refine WP.mono (e₂.base (rd := .a6) (by decide) 3) fun s₃ ⟨⟨a6, m₃⟩, k₃⟩ => ?_
  have e₃ := e₂.keep k₃ (by decide)
  have m03 : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  have k03 := (k₁.trans k₂).trans k₃
  -- `R² mod N` and `−N⁻¹`.
  refine WP.seq (WP.mono (hr2 e₃ ((k₂.trans k₃).gpr (by decide) |>.trans a2) ((k₃.gpr (by decide)).trans a5) a6
    (by rw [m03]; exact hn) hodd hN3 hP) fun s₄ ⟨⟨r₄, i₄⟩, o₄, k₄⟩ => ?_)
  rw [m03] at i₄ o₄
  have e₄ := e₃.keep k₄ (by decide)
  have n₄ : A s₄.mem B w 0 = N := by
    rw [A, Outside.wordsVal o₄ (by simp only [es]; omega) (by simp only [es]; omega)]; exact hn
  have wd₄ : word s₄.mem B (slot w 0) = word s.mem B (slot w 0) :=
    Outside.word o₄ (by simp only [es]; omega) (by simp only [es]; omega)
  -- `−N⁻¹` into header word 7.
  have hst : WP isa (.block [sth .t1 hMinv]) s₄ fun t =>
      t.mem = s₄.mem.writeW (off B 56) (s₄.gpr .t1) ∧ Keep [] s₄ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    simp only [sth, hMinv]
    brun [e₄.s6, e₄.hs.st (d := 56) (n := 8) (by omega), e₄.hs.al8 (d := 56) (by omega) (by decide)]
  refine WP.seq (WP.mono hst fun s₅ ⟨m₅, k₅⟩ => ?_)
  have e₅ := e₄.keep k₅ (by decide)
  have o₅ : Outside B 56 8 s₄.mem s₅.mem := by rw [m₅]; exact writeW_outside _ _ _ (by omega)
  -- 1 in array 7.
  refine WP.seq (WP.mono (Pub.oneP_ok e₅.hs (by omega) (by omega) (by simp only [es]; omega) e₅.a7 e₅.s5 e₅.t0)
    fun s₆ ⟨⟨r₆, o₆⟩, k₆⟩ => ?_)
  have e₆ := e₅.keep k₆ (by decide)
  have k46 := k₅.trans k₆
  have n₆ : A s₆.mem B w 0 = N := by
    rw [A, Outside.wordsVal o₆ (by simp only [es]; omega) (by simp only [es]; omega),
      Outside.wordsVal o₅ (by simp only [es]; omega) (by simp only [es]; omega)]; exact n₄
  have wd₆ : word s₆.mem B (slot w 0) = word s.mem B (slot w 0) := by
    rw [Outside.word o₆ (by simp only [es]; omega) (by simp only [es]; omega),
      Outside.word o₅ (by simp only [es]; omega) (by simp only [es]; omega), wd₄]
  have r1₆ : A s₆.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [A, Outside.wordsVal o₆ (by simp only [es]; omega) (by simp only [es]; omega),
      Outside.wordsVal o₅ (by simp only [es]; omega) (by simp only [es]; omega)]
    rw [show wordsVal s₄.mem B (slot w 1) w = A s₄.mem B w 1 from rfl, r₄, ← Nat.pow_add]
    congr 2; omega
  have t1₆ : s₆.gpr .t1 = s₄.gpr .t1 := k46.gpr (by decide)
  -- `R mod N` in array 6, the product of `R² mod N` and 1.
  refine WP.seq (WP.mono (Pub.montOp_ok e₆.hs (o := 6) (a := 1) (b := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by omega) (by omega) (by simp only [es]; omega) e₆.a7 e₆.s5
    e₆.t0 (by have := i₄; rw [← wd₆, ← t1₆] at this; exact this) (by
      rw [show wordsVal s₆.mem B (slot w 7) w = VG.Proof.Bignum.RISCV64.Pub.V s₆.mem B w 7 from rfl, r₆,
        show wordsVal s₆.mem B (slot w 0) w = A s₆.mem B w 0 from rfl, n₆]; omega))
    fun s₇ ⟨⟨lt₇, eq₇, o₇⟩, k₇⟩ => ?_)
  have e₇ := e₆.keep k₇ (by decide)
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  rw [show wordsVal s₆.mem B (slot w 0) w = A s₆.mem B w 0 from rfl, n₆,
    show wordsVal s₆.mem B (slot w 1) w = A s₆.mem B w 1 from rfl, r1₆,
    show wordsVal s₆.mem B (slot w 7) w = VG.Proof.Bignum.RISCV64.Pub.V s₆.mem B w 7 from rfl, r₆, Nat.mul_one,
    Nat.mod_mod] at eq₇
  rw [show wordsVal s₆.mem B (slot w 0) w = A s₆.mem B w 0 from rfl, n₆] at lt₇
  have r6₇ : A s₇.mem B w 6 = 2 ^ (64 * w) % N := by
    rw [A, ← Nat.mod_eq_of_lt lt₇]; exact VG.Proof.Bignum.mont_cancel hR eq₇
  have hnw28 : B.toNat + slot w 28 ≤ 2 ^ 64 := by omega
  have n₇ : A s₇.mem B w 0 = N := by
    rw [VG.Proof.MillerRabin.RISCV64.arr_eq o₇ (by decide) (by decide) hnw28, n₆]
  have r1₇ : A s₇.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [VG.Proof.MillerRabin.RISCV64.arr_eq o₇ (by decide) (by decide) hnw28, r1₆]
  have wd₇ : word s₇.mem B (slot w 0) = word s.mem B (slot w 0) := by
    rw [show word s₇.mem B (slot w 0) = VG.Proof.Bignum.word s₇.mem B (slot w 0) from rfl,
      (VG.Proof.Bignum.Frm.of_arrays (rs := [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))])
        o₇ (by simp)).word_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;>
          simp only [es] <;> omega) (by simp only [es]; omega)]
    exact wd₆
  have t1₇ : s₇.gpr .t1 = s₄.gpr .t1 := (k₇.gpr (by decide)).trans t1₆
  -- `N − R mod N` in array 10.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (e₇.base (rd := .a5) (by decide) 0) fun s₈ ⟨⟨b5, m₈⟩, k₈⟩ => ?_
  have e₈ := e₇.keep k₈ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e₈.base (rd := .a6) (by decide) 10) fun s₉ ⟨⟨b6, m₉⟩, k₉⟩ => ?_
  have e₉ := e₈.keep k₉ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e₉.base (rd := .t2) (by decide) 6) fun s₁₀ ⟨⟨b2, m₁₀⟩, k₁₀⟩ => ?_
  have e₁₀ := e₉.keep k₁₀ (by decide)
  have h7b : WP isa (.block [.addi .a7 .t2 0]) s₁₀ fun t =>
      (t.gpr .a7 = off B (slot w 6) ∧ t.mem = s₁₀.mem) ∧ Keep [.a7] s₁₀ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [b2, BitVec.add_zero]
  refine WP.mono h7b fun s₁₁ ⟨⟨b7, m₁₁⟩, k₁₁⟩ => ?_
  have k811 := ((k₈.trans k₉).trans k₁₀).trans k₁₁
  have m811 : s₁₁.mem = s₇.mem := by rw [m₁₁, m₁₀, m₉, m₈]
  refine WP.seq (WP.mono (subMod64_ok (e₇.hs.congr k811.2.2) (((k₉.trans k₁₀).trans k₁₁).gpr (by decide) |>.trans b5)
    ((k₁₀.trans k₁₁).gpr (by decide) |>.trans b6) b7 ((k811.gpr (by decide)).trans e₇.t0) (by omega) (by omega)
    (al 0) (al 10) (al 6) (by simp only [es]; omega) (by simp only [es]; omega) (by simp only [es]; omega)
    (by simp only [es]; omega) (by simp only [es]; omega)) fun s₁₂ ⟨⟨c, hc, hsub, _⟩, o₁₂, k₁₂⟩ => ?_)
  rw [m811, show wordsVal s₇.mem B (slot w 0) w = A s₇.mem B w 0 from rfl, n₇,
    show wordsVal s₇.mem B (slot w 6) w = A s₇.mem B w 6 from rfl, r6₇] at hsub
  have r10₁₂ : A s₁₂.mem B w 10 = N - 2 ^ (64 * w) % N := by
    have hx : wordsVal s₁₂.mem B (slot w 10) w < 2 ^ (64 * w) := wordsVal_lt _ _ _ _
    have hm := Nat.mod_lt (2 ^ (64 * w)) (show 0 < N by omega)
    have hNR : N < 2 ^ (64 * w) := by rw [← n₇]; exact wordsVal_lt _ _ _ _
    rw [A]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;> omega
  have k712 := k811.trans k₁₂
  rw [← m811] at n₇ r1₇ wd₇ r6₇
  have n₁₂ : A s₁₂.mem B w 0 = N := by
    rw [A, Outside.wordsVal o₁₂ (by simp only [es]; omega) (by simp only [es]; omega)]; exact n₇
  have r1₁₂ : A s₁₂.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [A, Outside.wordsVal o₁₂ (by simp only [es]; omega) (by simp only [es]; omega)]; exact r1₇
  have r6₁₂ : A s₁₂.mem B w 6 = 2 ^ (64 * w) % N := by
    rw [A, Outside.wordsVal o₁₂ (by simp only [es]; omega) (by simp only [es]; omega)]; exact r6₇
  have wd₁₂ : word s₁₂.mem B (slot w 0) = word s.mem B (slot w 0) := by
    rw [Outside.word o₁₂ (by simp only [es]; omega) (by simp only [es]; omega)]; exact wd₇
  -- `a7` back at array 0.
  have h7c : WP isa (.block [.addi .a7 .s6 hdrBytes]) s₁₂ fun t =>
      (t.gpr .a7 = off B (slot w 0) ∧ t.mem = s₁₂.mem) ∧ Keep [.a7] s₁₂ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [(k712.gpr (by decide)).trans e₇.s6, hdrBytes]
    simp only [slot, Nat.zero_mul, Nat.add_zero]; rfl
  refine WP.seq (WP.mono h7c fun s₁₃ ⟨⟨c7, m₁₃⟩, k₁₃⟩ => ?_)
  have k713 := k712.trans k₁₃
  have e₁₃ : Env s₁₃ B Z w := ⟨e₇.hs.congr k713.2.2, c7, (k713.gpr (by decide)).trans e₇.s5,
    (k713.gpr (by decide)).trans e₇.t0, (k713.gpr (by decide)).trans e₇.s6, hw4, hw128, hZ⟩
  have t1₁₃ : s₁₃.gpr .t1 = s₄.gpr .t1 := (k713.gpr (by decide)).trans t1₇
  have c₁₃ : MCtx s₁₃ B Z w N := ⟨e₁₃.hs, hw4, hw128, hZ, c7, e₁₃.s5, e₁₃.t0,
    by rw [t1₁₃, m₁₃, wd₁₂]; exact i₄, by rw [m₁₃]; exact n₁₂⟩
  -- `R mod N` copied into array 9.
  refine WP.seq (WP.mono (copy_ok c₁₃ (o := 9) (a := 6) (by decide) (by decide) (by decide))
    fun s₁₄ ⟨⟨cp, o₁₄⟩, k₁₄⟩ => ?_)
  have k714 := k713.trans k₁₄
  have e₁₄ : Env s₁₄ B Z w := e₁₃.keep k₁₄ (by decide)
  rw [m₁₃] at cp o₁₄
  have n₁₄ : A s₁₄.mem B w 0 = N := by
    rw [A, Outside.wordsVal o₁₄ (by simp only [es]; omega) (by simp only [es]; omega)]; exact n₁₂
  -- Miller–Rabin's exponent.
  refine WP.mono (expSetup_ok e₁₄ n₁₄ hodd (by omega)) fun t ⟨⟨eE, mE, oE⟩, kE⟩ => ?_
  have tv : ∀ j, j = 0 ∨ j = 1 ∨ j = 9 ∨ j = 10 → A t.mem B w j = A s₁₄.mem B w j := fun j hj => by
    rw [A, A, Outside.wordsVal oE (by rcases hj with rfl | rfl | rfl | rfl <;> simp only [es, aE] <;> omega)
      (by rcases hj with rfl | rfl | rfl | rfl <;> simp only [es] <;> omega)]
  have v14 : ∀ j, j = 0 ∨ j = 1 ∨ j = 10 → A s₁₄.mem B w j = A s₁₂.mem B w j := fun j hj => by
    rw [A, A, Outside.wordsVal o₁₄ (by rcases hj with rfl | rfl | rfl <;> simp only [es] <;> omega)
      (by rcases hj with rfl | rfl | rfl <;> simp only [es] <;> omega)]
  -- Word 56 and `N`'s low word, through the writes after the store.
  have w56 : word t.mem B 56 = s₄.gpr .t1 := by
    rw [Outside.word oE (by simp only [es, aE]; omega) (by omega), Outside.word o₁₄ (by simp only [es]; omega) (by omega),
      Outside.word o₁₂ (by simp only [es]; omega) (by omega), m811,
      show word s₇.mem B 56 = VG.Proof.Bignum.word s₇.mem B 56 from rfl,
      (VG.Proof.Bignum.Frm.of_arrays (rs := [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))])
        o₇ (by simp)).word_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;>
          simp only [es] <;> omega) (by omega),
      show VG.Proof.Bignum.word s₆.mem B 56 = word s₆.mem B 56 from rfl,
      Outside.word o₆ (by simp only [es]; omega) (by omega), m₅]
    exact word_writeW_self _ _ _ _
  have w0 : word t.mem B (slot w 0) = word s.mem B (slot w 0) := by
    rw [Outside.word oE (by simp only [es, aE]; omega) (by simp only [es]; omega),
      Outside.word o₁₄ (by simp only [es]; omega) (by simp only [es]; omega), wd₁₂]
  have t1t : t.gpr .t1 = s₄.gpr .t1 := ((k₁₄.trans kE).gpr (by decide)).trans t1₁₃
  refine ⟨⟨e₁₄.keep kE (by decide), by rw [tv 0 (by decide), n₁₄], by rw [w0, w56]; exact i₄,
    by rw [w0, t1t]; exact i₄, by rw [tv 1 (by decide), v14 1 (by decide), r1₁₂],
    by rw [tv 9 (by decide), cp, A, Outside.wordsVal o₁₂ (by simp only [es]; omega) (by simp only [es]; omega)];
       exact r6₇,
    by rw [tv 10 (by decide), v14 10 (by decide), r10₁₂], eE, mE, ?_⟩, ?_⟩
  · refine (outs_of o₄ ⟨(slot w 1, 24 * (w + 2)), by simp [mpRanges], by omega, by omega⟩).trans
      ((outs_of o₅ ⟨(56, 8), by simp [mpRanges], by omega, by omega⟩).trans
      ((outs_of o₆ ⟨(slot w 6, 16 * (w + 2)), by simp [mpRanges], by simp only [es]; omega,
        by simp only [es]; omega⟩).trans ?_))
    refine (Outs.cover (rs := [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))])
      (fun x hx => o₇ x fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hx (slot w 2, 8 * (w + 2)) (by simp)
        · exact hx (slot w 3, 8 * (w + 2)) (by simp)
        · exact hx (slot w 6, 8 * (w + 2)) (by simp)) fun r hr => ?_).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨(slot w 1, 24 * (w + 2)), by simp [mpRanges], by simp only [es]; omega, by simp only [es]; omega⟩
      · exact ⟨(slot w 1, 24 * (w + 2)), by simp [mpRanges], by simp only [es]; omega, by simp only [es]; omega⟩
      · exact ⟨(slot w 6, 16 * (w + 2)), by simp [mpRanges], by simp only [es]; omega, by simp only [es]; omega⟩
    rw [← m811]
    refine (outs_of o₁₂ ⟨(slot w 9, 16 * (w + 2)), by simp [mpRanges], by simp only [es]; omega,
      by simp only [es]; omega⟩).trans ?_
    exact (outs_of o₁₄ ⟨(slot w 9, 16 * (w + 2)), by simp [mpRanges], by omega, by simp only [es]; omega⟩).trans
      (outs_of oE ⟨(slot w aE, 8 * (w + 2)), by simp [mpRanges], by omega, by omega⟩)
  · exact ((((((((k03.trans k₄).trans k₅).trans k₆).trans k₇).trans k811).trans k₁₂).trans
      ((k₁₃.trans k₁₄).trans kE))).mono (by decide)

/-- `montPrepWith_ok` for `montPrepHi`, for `N` above `2^(64 (w − 1))`. -/
theorem montPrepHi_ok {s : State} {B : Addr} {Z w N : Nat} (h : Env s B Z w) (hn : A s.mem B w 0 = N)
    (hodd : N % 2 = 1) (hN3 : 3 ≤ N) (hNt : 2 ^ (64 * (w - 1)) < N) :
    WP isa montPrepHi s fun t =>
      (Env t B Z w ∧ A t.mem B w 0 = N ∧
        ((word t.mem B (slot w 0)).toNat * (word t.mem B 56).toNat + 1) % 2 ^ 64 = 0 ∧
        ((word t.mem B (slot w 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0 ∧
        A t.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧ A t.mem B w 9 = 2 ^ (64 * w) % N ∧
        A t.mem B w 10 = N - 2 ^ (64 * w) % N ∧ A t.mem B w aE = mrE N ∧
        t.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA N % 64) ∧
        Outs B (mpRanges w) s.mem t.mem) ∧ Keep mpRegs s t :=
  montPrepWith_ok r2_r2Ok h hn hodd hN3 hNt

/-! ## Copies within the working space -/

/-- `copyWords`, `w` words from `dS` (`t4`) to `dD` (`t3`) of the working
space, apart. -/
theorem copyWithin_ok {s : State} {B : Addr} {Z dS dD w : Nat} (hs : Scr s B Z)
    (h4 : s.gpr .t4 = off B dS) (h3 : s.gpr .t3 = off B dD) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hS : dS + 8 * w ≤ Z) (hD : dD + 8 * w ≤ Z) (aS : dS % 8 = 0) (aD : dD % 8 = 0)
    (hsep : dS + 8 * w ≤ dD ∨ dD + 8 * w ≤ dS) :
    WP isa Impl.Bignum.RISCV64.Precompute.copyWords s fun t =>
      (t.gpr .t3 = off B (dD + 8 * w) ∧ (∀ i < w, word t.mem B (dD + 8 * i) = word s.mem B (dS + 8 * i)) ∧
        Outside B dD (8 * w) s.mem t.mem) ∧ Keep [.s0, .t3, .t4, .t5] s t := by
  have hnw := hs.nowrap
  unfold Impl.Bignum.RISCV64.Precompute.copyWords
  have hpre : WP isa (.block [.addi .t5 .t0 0]) s fun s₁ =>
      (s₁.gpr .t5 = BitVec.ofNat 64 w ∧ s₁.mem = s.mem) ∧ Keep [.t5] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [ht0, BitVec.add_zero]
  refine WP.seq (WP.mono hpre fun s₁ ⟨⟨i5, im⟩, k₁⟩ => ?_)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (dD + 8 * i) ∧ t.gpr .t4 = off B (dS + 8 * i) ∧ Outside B dD (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (dD + 8 * k) = word s.mem B (dS + 8 * k)) ∧ Keep [.s0, .t3, .t4, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8,
      .addi .t4 .t4 8] ++ ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w) (by omega) (by omega) Inv
    (fun i hi t ⟨j3, j4, jout, jc, jk⟩ hc => ?_)
    ⟨by rw [k₁.gpr (by decide), h3]; rfl, by rw [k₁.gpr (by decide), h4]; rfl,
      by rw [← im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega), k₁.mono (by decide)⟩ i5)
    fun t ⟨t3, _, tout, tc, tk⟩ => ⟨⟨t3, tc, tout⟩, tk⟩
  have hsrc : word t.mem B (dS + 8 * i) = word s.mem B (dS + 8 * i) :=
    Outside.word jout (by omega) (by omega)
  have hs' := hs.congr jk.2.2
  have hst : WP isa (.block [.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8,
      .addi .t5 .t5 (-1)]) t
      fun t' => (t'.mem = t.mem.writeW (off B (dD + 8 * i)) (word t.mem B (dS + 8 * i)) ∧
        t'.gpr .t3 = off B (dD + 8 * i + 8) ∧ t'.gpr .t4 = off B (dS + 8 * i + 8) ∧
        t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ∧ Keep [.s0, .t3, .t4, .t5] t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [j3, j4, hs'.ld (show dS + 8 * i + 8 ≤ Z by omega), hs'.al8 (show dS + 8 * i + 8 ≤ Z by omega) (by omega),
      hs'.st (show dD + 8 * i + 8 ≤ Z by omega), hs'.al8 (show dD + 8 * i + 8 ≤ Z by omega) (by omega),
      BitVec.add_zero]
  refine WP.mono hst fun t' ⟨⟨e, l3, l4, l5⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l5⟩
  · rw [l3, show dD + 8 * i + 8 = dD + 8 * (i + 1) by omega]
  · rw [l4, show dS + 8 * i + 8 = dS + 8 * (i + 1) by omega]
  · have hw8 := writeW_outside t.mem B (d := dD + 8 * i) (word t.mem B (dS + 8 * i)) (by omega)
    rw [e]; exact (jout.mono (Nat.le_refl _) (by omega)).trans (hw8.mono (by omega) (by omega))
  · intro k hk
    have hw8 := writeW_outside t.mem B (d := dD + 8 * i) (word t.mem B (dS + 8 * i)) (by omega)
    rw [e]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [Outside.word hw8 (by omega) (by omega)]; exact jc k hk
    · rw [word_writeW_self, hsrc]

end VG.Proof.MillerRabin.RISCV64.Search
