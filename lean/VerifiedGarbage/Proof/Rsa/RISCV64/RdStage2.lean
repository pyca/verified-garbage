module

public import VerifiedGarbage.Proof.Rsa.RISCV64.RdOps
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyDiv
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyInv
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The second stage of `vg_rsa_recover_primes_det` on RISC-V

From the GCD on, what `Impl/Rsa/RISCV64/RecoverDet.lean`'s pieces compute,
each as an operation on the working space (`Ws`) from the numbers it reads to
what `Proof/Rsa/RecoverDetModel.lean` names, in the narrow (`w` words, 63
arrays) or the wide (`W2 w` words, 31 arrays) view:

* `divA_ok`: `a = g · 2^k x mod 2^wb`, `m = ⌊a / n⌋`, `r = a mod n` and
  whether `m < n`;
* `divB_ok`: `m + 1`, `n - r`, their quotient and remainder, and whether it is
  zero;
* `minus4n_ok`: `b`, `b²`, `4 n`, `b² - 4 n` and its two checks;
* `sqrtBody_ok`, `sqrt_ok`: a step of the square root is `sqrtStep`
  (`sqrtStep_code`), and `wb / 2` of them;
* `maskOf_ok`, `factors_ok`: the factors and the mask of every check.

Every frame is in the narrow view; `st2Regs` are the registers the steps may
change.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Loops
  VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr ptrs sub3 subN mov seqs copy sel half eqS stBorrow)

open VG.Impl.Rsa.RISCV64.Div (div)
open VG.Impl.Rsa.RISCV64.RecoverDet (ctxW ctxw shl shlC mulLow divA divB minus4n sqrtBody sqrt factors
  maskOf next wN wA wR wDt wT2 wG wX3 wB wSq wOne aN aZero aOne aNeg1 aM1 aD aRem aDt aRm aSy aTy aDf
  aP aQ aNy sLt sExact sC1 sC2 sBb sOk5 sMask sB0 sB1)
open VG.Proof.Rsa.RecoverDet (wsub sqrtStep sqrtStep_code sqOf fourN prod_iter)

/-- The registers the steps of the second stage may change. -/
abbrev st2Regs : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .a5, .s7, .a2, .a3, .a6, .s8, .s9, .s10]

/-! ## Helpers -/

/-- `sub3`, and only the first `w` words of `o` change. -/
theorem sub3o_ok {s : State} {B : Addr} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 2048)
    (aA : Ahead (arr w o) (arr w a) w) (aB : Ahead (arr w o) (arr w b) w) :
    WP isa (sub3 o a b) s fun t => Ws t B Z w N ∧ Frame B w [o] [] s.mem t.mem ∧
      Outside B (arr w o) (8 * w) s.mem t.mem ∧
      num t.mem B w o + num s.mem B w b = num s.mem B w a + 2 ^ (64 * w) * (t.gpr .t4).toNat ∧
      (t.gpr .t4).toNat ≤ 1 ∧ Keep opRegs s t := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  rw [sub3, subN, WP.seq_iff]
  refine ptrs_ok h (by omega_arith) (by omega_arith) (by omega_arith) fun t p0 p1 p2 kt mt => ?_
  have hb' : WP isa (.block [.addi .t3 .s9 ((0 : Nat) : Int), .li .t4 0]) t fun u =>
      (u.gpr .t0 = off B (arr w o) ∧ u.gpr .t1 = off B (arr w a) ∧ u.gpr .t2 = off B (arr w b) ∧
        u.gpr .t3 = BitVec.ofNat 64 w ∧ u.gpr .t4 = 0 ∧ u.mem = t.mem) ∧ Keep [.t3, .t4] t u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_addi_nat (show (0 : Nat) < 2048 by omega_arith), fin64_exec_li_zero, p0, p1, p2,
      (h.of_keep kt).s9, add_ofNat_zero']
  refine WP.mono hb' fun u ⟨⟨u0, u1, u2, u3, u4, um⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := (kt.trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  refine WP.mono (subLoop_ok hu.scr u0 u1 u2 u3 (by rw [u4]; decide) (by omega_arith) (by omega_arith)
    (arr_al _ _) (arr_al _ _) (arr_al _ _) (by omega_arith) (by omega_arith) (by omega_arith) aA aB) ?_
  intro t' ⟨b4, veq, out, kt'⟩
  rw [u4, um, mt] at veq
  rw [um, mt] at out
  exact ⟨hu.of_keep kt', Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega_arith) (by simp), out, by simpa using veq, b4, Keep.trans' k₁ kt'⟩

/-- A subtraction modulo `2^b` as the code leaves it, and its borrow. -/
theorem wsub_of_sub {b x a c β : Nat} (hv : x + c = a + 2 ^ b * β) (hx : x < 2 ^ b)
    (hc : c < 2 ^ b) (hβ : β ≤ 1) : x = wsub b a c ∧ (β = 1 ↔ a < c) := by
  unfold wsub
  rcases (by omega : β = 0 ∨ β = 1) with rfl | rfl
  · simp only [Nat.mul_zero, Nat.add_zero] at hv
    refine ⟨?_, by omega⟩
    rw [show a + 2 ^ b - c = x + 2 ^ b by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hx]
  · simp only [Nat.mul_one] at hv
    refine ⟨?_, by omega⟩
    rw [show a + 2 ^ b - c = x by omega, Nat.mod_eq_of_lt hx]

/-- `b²` as the model computes it. -/
theorem sqOf_eq {nb wb b : Nat} (hb : b < 2 ^ nb) (hw : nb ≤ wb) : sqOf nb wb b = b * b % 2 ^ wb := by
  have : b < 2 ^ wb := Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) hw)
  unfold sqOf
  rw [prod_iter _ _ _ this]
  simp only
  rw [Nat.mod_eq_of_lt hb]

/-- The upper half of a wide array, apart from a write of the low `w` words of its low half. -/
theorem hiW_out {m m' : Mem} {B : Addr} {w j : Nat} (h : Outside B (arr w (2 * j)) (8 * w) m m')
    (fit : arr w (2 * j + 1) + 8 * w ≤ 2 ^ 64) : hiW m' B w j = hiW m B w j := by
  have := arr_succ w (2 * j)
  have hS : S w = 8 * (w + 2) := rfl
  exact Mont.Outside.wordsVal h (by omega_arith) (by omega_arith)

/-- The upper half of a wide array, apart from a frame of other narrow arrays. -/
theorem hiW_frame {m m' : Mem} {B : Addr} {w j : Nat} {js ds : List Nat} (f : Frame B w js ds m m')
    (hj : ∀ k ∈ js, k ≠ 2 * j ∧ k ≠ 2 * j + 1) (hd : ∀ d ∈ ds, d + 8 ≤ hdr)
    (fit : arr w (2 * j + 1) + S w ≤ 2 ^ 64) : hiW m' B w j = hiW m B w j := by
  have := arr_succ w (2 * j)
  have hS : S w = 8 * (w + 2) := rfl
  refine f.words (fun k hk => ?_) (fun d hd' => ?_) (by omega_arith)
  · obtain ⟨h1, h2⟩ := hj k hk
    rcases Nat.lt_or_gt_of_ne h1 with c | c
    · have := arr_end (w := w) c; omega_arith
    · have c' : 2 * j + 1 < k := by omega
      have := arr_end (w := w) c'; omega_arith
  · have := hd d hd'; have := hdr_le_arr w (2 * j); omega_arith

/-- The number of a wide array read in the narrow view is its value modulo `2^(64 w)`. -/
theorem st2_num_low_of {m : Mem} {B : Addr} {w j v : Nat} (hv : num m B (W2 w) j = v) :
    num m B w (2 * j) = v % 2 ^ (64 * w) := by rw [num_low, hv]

/-! ## `a`, `m` and `r` -/

theorem divA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w 63) (hW : W2 w ≤ 1024)
    (hNz : hiW s.mem B w wN = 0) (hNt : word s.mem B (arr w (2 * wN + 1) + 8 * w) = 0)
    (hA0 : num s.mem B (W2 w) wA = 0) :
    WP isa divA s fun t => Ws t B Z (W2 w) 31 ∧
      Frame B w (halves [wN, wA, wR, wDt, wT2]) [sLt] s.mem t.mem ∧ Keep st2Regs s t ∧
      (0 < num s.mem B w aN →
        num t.mem B (W2 w) wN = num s.mem B w aN ∧
        num t.mem B (W2 w) wA =
          num s.mem B (W2 w) wG * num s.mem B (W2 w) wX3 % 2 ^ (64 * W2 w) / num s.mem B w aN ∧
        num t.mem B (W2 w) wR =
          num s.mem B (W2 w) wG * num s.mem B (W2 w) wX3 % 2 ^ (64 * W2 w) % num s.mem B w aN ∧
        slot t.mem B sLt = (if num s.mem B (W2 w) wG * num s.mem B (W2 w) wX3 % 2 ^ (64 * W2 w) /
          num s.mem B w aN < num s.mem B w aN then 1 else 0)) := by
  have fit : ∀ j < 63, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  unfold divA
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (o := 2 * wN) (a := aN) (by decide) (by decide) (by decide) (by decide))
    fun t1 ⟨h1, f1, v1, r1, o1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxW_ok (M := 31) h1 hW (by decide)) fun t2 ⟨⟨h2, m2⟩, r2⟩ => ?_
  have fW : ∀ j < 31, arr (W2 w) j + S (W2 w) ≤ 2 ^ 64 := fun j hj => h2.fit64 hj
  have f1W := f1.toWide
  rw [← m2] at f1 f1W o1 v1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have a2 : num t2.mem B (W2 w) wA = 0 := by
    rw [f1W.num (by decide) (by simp) (fW _ (by decide)), hA0]
  have g2 : num t2.mem B (W2 w) wG = num s.mem B (W2 w) wG := f1W.num (by decide) (by simp) (fW _ (by decide))
  have x2 : num t2.mem B (W2 w) wX3 = num s.mem B (W2 w) wX3 :=
    f1W.num (by decide) (by simp) (fW _ (by decide))
  have hz2 : hiW t2.mem B w wN = 0 := by
    have f29 : arr w (2 * wN + 1) + 8 * w ≤ 2 ^ 64 := by
      have := fit (2 * wN + 1) (by decide); simp only [S] at this; omega_arith
    rw [hiW_out o1 f29]; exact hNz
  have n2 : num t2.mem B (W2 w) wN = num s.mem B w aN := by
    rw [numW_low (j := wN) hz2]; exact v1
  refine WP.mono (mulLow_ok h2 (o := wA) (y := wG) (x := wX3) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) a2) fun t3 ⟨h3, f3, _, v3, r3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have n3 : num t3.mem B (W2 w) wN = num s.mem B w aN := by
    rw [f3.num (by decide) (by simp) (fW _ (by decide)), n2]
  have z3 : word t3.mem B (arr (W2 w) wN + 8 * W2 w) = 0 := by
    rw [wideTop, f3.toNarrow.word (by omega_arith) (by decide) (by simp) (fit _ (by decide)),
      f1.word (by omega_arith) (by decide) (by simp) (fit _ (by decide)), hNt]
  refine WP.mono (div_ok h3 (q := wA) (r := wR) (d := wN) (t := wDt) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) z3)
    fun t4 ⟨h4, f4, r4, _, v4⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have n4 : num t4.mem B (W2 w) wN = num s.mem B w aN := by
    rw [f4.num (by decide) (by simp) (fW _ (by decide)), n3]
  refine WP.mono (sub3_ok h4 (o := wT2) (a := wA) (b := wN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t5 ⟨h5, f5, v5, b5, r5⟩ => ?_
  refine WP.mono (stBorrow_ok h5 (sl := sLt) (by decide) (by decide)) fun t ⟨h6, f6, s6, r6⟩ => ?_
  refine ⟨h6, ?_, ?_, fun hn => ?_⟩
  · exact (((((f1.mono (js' := halves [wN, wA, wR, wDt, wT2]) (ds' := [sLt]) (by decide) (by simp)).trans
      (f3.toNarrow.mono (by decide) (by simp))).trans (f4.toNarrow.mono (by decide) (by simp))).trans
      (f5.toNarrow.mono (by decide) (by simp))).trans (f6.toNarrow.mono (by decide) (by decide)))
  · exact Keep.trans' (r1.mono (by decide)) (Keep.trans' (r2.mono (by decide)) (Keep.trans'
      (r3.mono (by decide)) (Keep.trans' (r4.mono (by decide)) (Keep.trans' (r5.mono (by decide))
        (r6.mono (by decide))))))
  · rw [g2, x2] at v3
    obtain ⟨q4, -, r4', -⟩ := v4 (by rw [n3]; exact hn)
    rw [v3, n3] at q4 r4'
    have e5 : ∀ j, j < 31 → j ≠ wT2 → num t.mem B (W2 w) j = num t4.mem B (W2 w) j := fun j hj hj' => by
      rw [f6.num (by simp) (by decide) (fW _ hj), f5.num (by simpa using fun e => hj' e.symm) (by simp) (fW _ hj)]
    rw [e5 _ (by decide) (by decide), e5 _ (by decide) (by decide), e5 _ (by decide) (by decide), n4, q4, r4', s6]
    refine ⟨rfl, rfl, rfl, ?_⟩
    have W := (wsub_of_sub v5 (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _) b5).2
    rw [q4, n4] at W
    split
    · exact W.mpr (by assumption)
    · rename_i c
      omega

/-! ## `b - 1` -/

/-- `-1` as the code leaves it. -/
theorem st2_neg_one_of {x β P : Nat} (hv : x + 1 = 0 + P * β) (hβ : β ≤ 1) : x = P - 1 := by
  rcases (by omega : β = 0 ∨ β = 1) with rfl | rfl <;> simp at hv <;> omega

/-- `m + 1` as the code leaves it: `m - (P - 1)`. -/
theorem st2_m1_of {x m β P : Nat} (hv : x + (P - 1) = m + P * β) (hx : x < P) (hm : m < P) (hβ : β ≤ 1) :
    x = (m + 1) % P := by
  rcases (by omega : β = 0 ∨ β = 1) with rfl | rfl
  · simp at hv
    have : m = P - 1 := by omega
    subst this; rw [show P - 1 + 1 = P by omega, Nat.mod_self]; omega
  · simp at hv; rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem divB_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z (W2 w) 31) (hfit : arr w 63 ≤ Z)
    (hw : 0 < w) (hZ0 : num s.mem B w aZero = 0) (hOne : num s.mem B w aOne = 1)
    (hM1t : word s.mem B (arr w aM1 + 8 * w) = 0) :
    WP isa divB s fun t => Ws t B Z w 63 ∧
      Frame B w [aNeg1, aM1, aD, aRem, aDt] [sExact] s.mem t.mem ∧ Keep st2Regs s t ∧
      num t.mem B w aNeg1 = 2 ^ (64 * w) - 1 ∧
      num t.mem B w aM1 = (num s.mem B (W2 w) wA % 2 ^ (64 * w) + 1) % 2 ^ (64 * w) ∧
      (0 < num t.mem B w aM1 →
        num t.mem B w aD = wsub (64 * w) (num s.mem B w aN) (num s.mem B (W2 w) wR % 2 ^ (64 * w)) /
          num t.mem B w aM1 ∧
        num t.mem B w aRem = wsub (64 * w) (num s.mem B w aN) (num s.mem B (W2 w) wR % 2 ^ (64 * w)) %
          num t.mem B w aM1) ∧
      slot t.mem B sExact = (if num t.mem B w aRem = 0 then 1 else 0) := by
  unfold divB
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxw_ok (N := 63) h hw hfit) fun t1 ⟨⟨h1, m1⟩, r1⟩ => ?_
  have fit : ∀ j < 63, arr w j + S w ≤ 2 ^ 64 := fun j hj => h1.fit64 hj
  have P1 : 1 ≤ 2 ^ (64 * w) := Nat.one_le_two_pow
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h1 (o := aNeg1) (a := aZero) (b := aOne) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t2 ⟨h2, f2, v2, b2, r2⟩ => ?_
  rw [m1, hZ0, hOne] at v2
  have neg2 := st2_neg_one_of v2 b2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3o_ok h2 (o := aM1) (a := 2 * wA) (b := aNeg1) (by decide) (by decide) (by decide)
    (by decide) (by simpa using ahead_of_ne (w := w) (o := aM1) (a := 2 * wA) (by decide) 0 (by decide))
    (by simpa using ahead_of_ne (w := w) (o := aM1) (a := aNeg1) (by decide) 0 (by decide)))
    fun t3 ⟨h3, f3, o3, v3, b3, r3⟩ => ?_
  have a2 : num t2.mem B w (2 * wA) = num s.mem B (W2 w) wA % 2 ^ (64 * w) := by
    rw [f2.num (by decide) (by simp) (fit _ (by decide)), m1, num_low]
  rw [a2, neg2] at v3
  have m3 := st2_m1_of v3 (wordsVal_lt _ _ _ _) (Nat.mod_lt _ (by omega)) b3
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h3 (o := aD) (a := aN) (b := 2 * wR) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t4 ⟨h4, f4, v4, b4, r4⟩ => ?_
  have n3 : num t3.mem B w aN = num s.mem B w aN := by
    rw [f3.num (by decide) (by simp) (fit _ (by decide)), f2.num (by decide) (by simp) (fit _ (by decide)), m1]
  have r3' : num t3.mem B w (2 * wR) = num s.mem B (W2 w) wR % 2 ^ (64 * w) := by
    rw [f3.num (by decide) (by simp) (fit _ (by decide)), f2.num (by decide) (by simp) (fit _ (by decide)),
      m1, num_low]
  rw [n3, r3'] at v4
  have d4 := (wsub_of_sub v4 (wordsVal_lt _ _ _ _) (Nat.mod_lt _ (by omega)) b4).1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have z4 : word t4.mem B (arr w aM1 + 8 * w) = 0 := by
    rw [f4.word (by omega_arith) (by decide) (by simp) (fit _ (by decide)),
      o3.word (by have := arr_succ w aM1; simp only [S] at this; omega_arith)
        (by have := fit aM1 (by decide); simp only [S] at this; omega_arith),
      f2.word (by omega_arith) (by decide) (by simp) (fit _ (by decide)), m1, hM1t]
  refine WP.mono (div_ok h4 (q := aD) (r := aRem) (d := aM1) (t := aDt) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) z4)
    fun t5 ⟨h5, f5, r5, _, v5⟩ => ?_
  refine WP.mono (eqS_ok h5 (d := sExact) (a := aRem) (b := aZero) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun t ⟨h6, f6, s6, r6⟩ => ?_
  have M4 : num t4.mem B w aM1 = num t3.mem B w aM1 := f4.num (by decide) (by simp) (fit _ (by decide))
  have M5 : num t5.mem B w aM1 = num t3.mem B w aM1 := by
    rw [f5.num (by decide) (by simp) (fit _ (by decide)), M4]
  have Mt : num t.mem B w aM1 = num t3.mem B w aM1 := by
    rw [f6.num (by simp) (by decide) (fit _ (by decide)), M5]
  have Z5 : num t5.mem B w aZero = 0 := by
    rw [f5.num (by decide) (by simp) (fit _ (by decide)), f4.num (by decide) (by simp) (fit _ (by decide)),
      f3.num (by decide) (by simp) (fit _ (by decide)), f2.num (by decide) (by simp) (fit _ (by decide)), m1, hZ0]
  have e6 : ∀ j < 63, num t.mem B w j = num t5.mem B w j := fun j hj => f6.num (by simp) (by decide) (fit _ hj)
  refine ⟨h6, ?_, ?_, ?_, ?_, fun hp => ?_, ?_⟩
  · rw [m1] at f2
    exact (((f2.mono (by decide) (by simp)).trans (f3.mono (by decide) (by simp))).trans
      (f4.mono (by decide) (by simp))).trans ((f5.mono (by decide) (by simp)).trans
        (f6.mono (by simp) (by decide)))
  · exact Keep.trans' (r1.mono (by decide)) (Keep.trans' (r2.mono (by decide)) (Keep.trans'
      (r3.mono (by decide)) (Keep.trans' (r4.mono (by decide)) (Keep.trans' (r5.mono (by decide))
        (r6.mono (by decide))))))
  · rw [e6 _ (by decide), f5.num (by decide) (by simp) (fit _ (by decide)),
      f4.num (by decide) (by simp) (fit _ (by decide)), f3.num (by decide) (by simp) (fit _ (by decide)), neg2]
  · rw [Mt, m3]
  · rw [Mt] at hp
    obtain ⟨q5, -, r5', -⟩ := v5 (by rw [M4]; exact hp)
    rw [e6 aD (by decide), e6 aRem (by decide), Mt, q5, r5', M4, ← d4]
    exact ⟨rfl, rfl⟩
  · rw [s6, Z5, e6 aRem (by decide)]

/-! ## `b² - 4 n` -/

/-- A doubling as the code leaves it. -/
theorem st2_dbl_of {x c y P : Nat} (hv : x + P * c = y) (hx : x < P) : x = y % P := by
  subst hv; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem minus4n_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w 63) (hW : W2 w ≤ 1024)
    (hNeg : num s.mem B w aNeg1 = 2 ^ (64 * w) - 1) (hBz : hiW s.mem B w wB = 0)
    (hSq0 : num s.mem B (W2 w) wSq = 0) (hOne : num s.mem B (W2 w) wOne = 1) :
    WP isa minus4n s fun t => Ws t B Z (W2 w) 31 ∧
      Frame B w (aD :: halves [wB, wSq, wN, wR, wT2]) [sC1, sC2] s.mem t.mem ∧ Keep st2Regs s t ∧
      num t.mem B w aD = (num s.mem B w aD + 1) % 2 ^ (64 * w) ∧
      num t.mem B (W2 w) wSq = num t.mem B w aD * num t.mem B w aD % 2 ^ (64 * W2 w) ∧
      num t.mem B (W2 w) wN = fourN (64 * W2 w) (num s.mem B (W2 w) wN) ∧
      num t.mem B (W2 w) wR = wsub (64 * W2 w) (num t.mem B (W2 w) wSq) (num t.mem B (W2 w) wN) ∧
      slot t.mem B sC1 = (if num t.mem B (W2 w) wSq < num t.mem B (W2 w) wN then 1 else 0) ∧
      slot t.mem B sC2 = (if num t.mem B (W2 w) wR < 1 then 1 else 0) := by
  have fit : ∀ j < 63, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have P1 : 1 ≤ 2 ^ (64 * w) := Nat.one_le_two_pow
  unfold minus4n
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have aN1 : Ahead (arr w aD) (arr w aNeg1) w := by
    simpa using ahead_of_ne (w := w) (o := aD) (a := aNeg1) (by decide) 0 (by decide)
  refine WP.mono (sub3_gen_ok h (o := aD) (a := aD) (b := aNeg1) (by decide) (by decide) (by decide)
    (by decide) (ahead_self _ _ _) aN1) fun t1 ⟨h1, f1, v1, b1, r1⟩ => ?_
  rw [hNeg] at v1
  have d1 := st2_m1_of v1 (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _) b1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h1 (o := 2 * wB) (a := aD) (by decide) (by decide) (by decide) (by decide))
    fun t2 ⟨h2, f2, v2, r2, o2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxW_ok (M := 31) h2 hW (by decide)) fun t3 ⟨⟨h3, m3⟩, r3⟩ => ?_
  have fW : ∀ j < 31, arr (W2 w) j + S (W2 w) ≤ 2 ^ 64 := fun j hj => h3.fit64 hj
  have f1W := f1.toWide
  have f2W := f2.toWide
  rw [← m3] at f2 f2W o2 v2
  have hz2 : hiW t3.mem B w wB = 0 := by
    have f37 : arr w (2 * wB + 1) + 8 * w ≤ 2 ^ 64 := by
      have := fit (2 * wB + 1) (by decide); simp only [S] at this; omega_arith
    rw [hiW_out o2 f37, hiW_frame f1 (by decide) (by simp) (fit _ (by decide)), hBz]
  have B3 : num t3.mem B (W2 w) wB = num t1.mem B w aD := by rw [numW_low (j := wB) hz2]; exact v2
  have D3 : num t3.mem B w aD = num t1.mem B w aD := by
    rw [f2.num (by decide) (by simp) (fit _ (by decide))]
  have Q3 : num t3.mem B (W2 w) wSq = 0 := by
    rw [f2W.num (by decide) (by simp) (fW _ (by decide)), f1W.num (by decide) (by simp) (fW _ (by decide)), hSq0]
  have N3 : num t3.mem B (W2 w) wN = num s.mem B (W2 w) wN := by
    rw [f2W.num (by decide) (by simp) (fW _ (by decide)), f1W.num (by decide) (by simp) (fW _ (by decide))]
  have O3 : num t3.mem B (W2 w) wOne = 1 := by
    rw [f2W.num (by decide) (by simp) (fW _ (by decide)), f1W.num (by decide) (by simp) (fW _ (by decide)), hOne]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mulLow_ok h3 (o := wSq) (y := wB) (x := wB) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) Q3) fun t4 ⟨h4, f4, _, v4, r4⟩ => ?_
  rw [B3] at v4
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shl_ok h4 (j := wN) (by decide) (by decide)) fun t5 ⟨h5, f5, _, v5, c5, r5⟩ => ?_
  rw [f4.num (by decide) (by simp) (fW _ (by decide)), N3] at v5
  have N5 := st2_dbl_of v5 (wordsVal_lt _ _ _ _)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shl_ok h5 (j := wN) (by decide) (by decide)) fun t6 ⟨h6, f6, _, v6, c6, r6⟩ => ?_
  rw [N5] at v6
  have N6 := st2_dbl_of v6 (wordsVal_lt _ _ _ _)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h6 (o := wR) (a := wSq) (b := wN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t7 ⟨h7, f7, v7, b7, r7⟩ => ?_
  have S6 : num t6.mem B (W2 w) wSq = num t4.mem B (W2 w) wSq := by
    rw [f6.num (by decide) (by simp) (fW _ (by decide)), f5.num (by decide) (by simp) (fW _ (by decide))]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (stBorrow_ok h7 (sl := sC1) (by decide) (by decide)) fun t8 ⟨h8, f8, s8, r8⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h8 (o := wT2) (a := wR) (b := wOne) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t9 ⟨h9, f9, v9, b9, r9⟩ => ?_
  refine WP.mono (stBorrow_ok h9 (sl := sC2) (by decide) (by decide)) fun t ⟨h10, f10, s10, r10⟩ => ?_
  -- What the last steps keep.
  have eW : ∀ j < 31, j ≠ wT2 → num t.mem B (W2 w) j = num t8.mem B (W2 w) j := fun j hj hj' => by
    rw [f10.num (by simp) (by decide) (fW _ hj), f9.num (by simpa using fun e => hj' e.symm) (by simp) (fW _ hj),
      f8.num (by simp) (by decide) (fW _ hj)]
  have e8 : ∀ j < 31, j ≠ wR → num t8.mem B (W2 w) j = num t6.mem B (W2 w) j := fun j hj hj' => by
    rw [f8.num (by simp) (by decide) (fW _ hj), f7.num (by simpa using fun e => hj' e.symm) (by simp) (fW _ hj)]
  have R8 : num t8.mem B (W2 w) wR = num t7.mem B (W2 w) wR := f8.num (by simp) (by decide) (fW _ (by decide))
  have One8 : num t8.mem B (W2 w) wOne = 1 := by
    rw [e8 _ (by decide) (by decide), f6.num (by decide) (by simp) (fW _ (by decide)),
      f5.num (by decide) (by simp) (fW _ (by decide)), f4.num (by decide) (by simp) (fW _ (by decide)), O3]
  have mo : ∀ {js ds : List Nat} {m m' : Mem}, Frame B (W2 w) js ds m m' →
      (∀ j ∈ halves js, j ∈ halves [wSq, wN, wR, wT2]) → (∀ d ∈ ds, d ∈ [sC1, sC2]) →
      Frame B w (halves [wSq, wN, wR, wT2]) [sC1, sC2] m m' := fun f hj hd => f.toNarrow.mono hj hd
  have fT : Frame B w (halves [wSq, wN, wR, wT2]) [sC1, sC2] t3.mem t.mem :=
    ((((((mo f4 (by decide) (by decide)).trans (mo f5 (by decide) (by decide))).trans
      (mo f6 (by decide) (by decide))).trans (mo f7 (by decide) (by decide))).trans
      (mo f8 (by decide) (by decide))).trans (mo f9 (by decide) (by decide))).trans
      (mo f10 (by decide) (by decide))
  have Dt : num t.mem B w aD = num t1.mem B w aD := by
    rw [fT.num (by decide) (by decide) (fit _ (by decide)), D3]
  have hSq : num t.mem B (W2 w) wSq = num t6.mem B (W2 w) wSq := by
    rw [eW _ (by decide) (by decide), e8 _ (by decide) (by decide)]
  have hN : num t.mem B (W2 w) wN = num t6.mem B (W2 w) wN := by
    rw [eW _ (by decide) (by decide), e8 _ (by decide) (by decide)]
  have hR : num t.mem B (W2 w) wR = num t7.mem B (W2 w) wR := by rw [eW _ (by decide) (by decide), R8]
  rw [R8, One8] at v9
  have W7 := wsub_of_sub v7 (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _) b7
  have W9 := wsub_of_sub v9 (wordsVal_lt _ _ _ _) (Nat.one_lt_two_pow (by simp only [W2]; omega)) b9
  refine ⟨h10, ?_, ?_, by rw [Dt, d1], by rw [hSq, Dt, S6, v4], by rw [hN, N6, fourN], ?_, ?_, ?_⟩
  · exact ((f1.mono (by decide) (by simp)).trans (f2.mono (by decide) (by simp))).trans
      (fT.mono (by decide) (by decide))
  · exact Keep.trans' (r1.mono (by decide)) (Keep.trans' (r2.mono (by decide)) (Keep.trans'
      (r3.mono (by decide)) (Keep.trans' (r4.mono (by decide)) (Keep.trans' (r5.mono (by decide))
        (Keep.trans' (r6.mono (by decide)) (Keep.trans' (r7.mono (by decide)) (Keep.trans' (r8.mono (by decide))
          (Keep.trans' (r9.mono (by decide)) (r10.mono (by decide))))))))))
  · rw [hR, hSq, hN, W7.1]
  · have S1 : slot t.mem B sC1 = slot t8.mem B sC1 := by
      rw [f10.slot (by decide) (by decide), f9.slot (by decide) (by simp)]
    rw [S1, s8, hSq, hN]
    split
    · exact W7.2.mpr (by assumption)
    · have := W7.2; omega
  · rw [s10, hR]
    split
    · exact W9.2.mpr (by assumption)
    · have := W9.2; omega

/-! ## The square root -/

/-- A shift as the code leaves it: the low bits and the bit shifted out. -/
theorem st2_shl_split {x c y Q : Nat} (hv : x + Q * c = y) (hx : x < Q) : x = y % Q ∧ c = y / Q := by
  subst hv
  have hQ : 0 < Q := by omega
  refine ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx], ?_⟩
  rw [Nat.add_comm, Nat.mul_add_div hQ, Nat.div_eq_of_lt hx, Nat.add_zero]

/-- `t4 := 1`. -/
theorem st2_li1_ok (s : State) :
    WP isa (.block [.li .t4 1]) s fun u => (u.gpr .t4 = 1#64 ∧ u.mem = s.mem) ∧ Keep [.t4] s u := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [keys_exec_li_one]

/-- `t4 := 1 - [sBb]`. -/
theorem notBb_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) :
    WP isa (.block [.load .d .t5 .s11 sBb, .logicImm .xor .t4 .t5 1]) s fun u =>
      (u.gpr .t4 = word s.mem B sBb ^^^ 1#64 ∧ u.mem = s.mem) ∧ Keep [.t4, .t5] s u := by
  have nw := h.nowrap
  have hz := h.hdr_le
  simp only [hdr_eq] at hz
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h.s11, h.scr.ld (d := sBb) (n := 8) (by simp only [sBb]; omega_arith),
    h.scr.al8 (d := sBb) (by simp only [sBb]; omega_arith) (by decide), show sBb < 2048 by decide,
    add_ofNat_zero']

/-- `s7 := s7 - 1`. -/
theorem st2_next_ok (s : State) :
    WP isa (.block next) s fun u =>
      (u.gpr .s7 = s.gpr .s7 - BitVec.ofNat 64 1 ∧ u.mem = s.mem) ∧ Keep [.s7] s u := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [next]

theorem sqrtBody_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w 63) (hW : W2 w ≤ 1024) :
    WP isa sqrtBody s fun t => Ws t B Z w 63 ∧
      Frame B w (halves [wR] ++ [aRm, aSy, aTy, aDf]) [sBb] s.mem t.mem ∧ Keep st2Regs s t ∧
      t.gpr .s7 = s.gpr .s7 - BitVec.ofNat 64 1 ∧
      (num t.mem B (W2 w) wR, num t.mem B w aRm, num t.mem B w aSy) =
        sqrtStep (64 * w) (64 * W2 w) (num s.mem B (W2 w) wR, num s.mem B w aRm, num s.mem B w aSy) := by
  have fit : ∀ j < 63, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have hw := h.wpos
  have hfit := h.fits
  unfold sqrtBody
  -- The first two bits of the radicand into the remainder.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxW_ok (M := 31) h hW (by decide)) fun t1 ⟨⟨h1, m1⟩, r1⟩ => ?_
  have fW : ∀ j < 31, arr (W2 w) j + S (W2 w) ≤ 2 ^ 64 := fun j hj => h1.fit64 hj
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shl_ok h1 (j := wR) (by decide) (by decide)) fun t2 ⟨h2, f2, _, v2, c2, r2⟩ => ?_
  rw [m1] at v2 f2
  have X2 := st2_shl_split v2 (wordsVal_lt _ _ _ _)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxw_ok (N := 63) h2 hw hfit) fun t3 ⟨⟨h3, m3⟩, r3⟩ => ?_
  have c3 : t3.gpr .t4 = t2.gpr .t4 := r3.gpr (by decide)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shlC_ok h3 (j := aRm) (by decide) (by decide) (by rw [c3]; exact c2))
    fun t4 ⟨h4, f4, _, v4, c4, r4⟩ => ?_
  rw [m3, c3, f2.toNarrow.num (by decide) (by simp) (fit _ (by decide))] at v4
  have R4 := (st2_shl_split v4 (wordsVal_lt _ _ _ _)).1
  rw [m3] at f4
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxW_ok (M := 31) h4 hW (by decide)) fun t5 ⟨⟨h5, m5⟩, r5⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shl_ok h5 (j := wR) (by decide) (by decide)) fun t6 ⟨h6, f6, _, v6, c6, r6⟩ => ?_
  rw [m5, f4.toWide.num (by decide) (by simp) (fW _ (by decide)), X2.1] at v6
  rw [m5] at f6
  have X6 := st2_shl_split v6 (wordsVal_lt _ _ _ _)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxw_ok (N := 63) h6 hw hfit) fun t7 ⟨⟨h7, m7⟩, r7⟩ => ?_
  have c7 : t7.gpr .t4 = t6.gpr .t4 := r7.gpr (by decide)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shlC_ok h7 (j := aRm) (by decide) (by decide) (by rw [c7]; exact c6))
    fun t8 ⟨h8, f8, _, v8, c8, r8⟩ => ?_
  rw [m7, c7, f6.toNarrow.num (by decide) (by simp) (fit _ (by decide)), X6.2] at v8
  rw [m7] at f8
  have R8 := (st2_shl_split v8 (wordsVal_lt _ _ _ _)).1
  -- `4 y + 1`.
  have Y8 : num t8.mem B w aSy = num s.mem B w aSy := by
    rw [f8.num (by decide) (by simp) (fit _ (by decide)), f6.toNarrow.num (by decide) (by simp) (fit _ (by decide)),
      f4.num (by decide) (by simp) (fit _ (by decide)), f2.toNarrow.num (by decide) (by simp) (fit _ (by decide))]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h8 (o := aTy) (a := aSy) (by decide) (by decide) (by decide) (by decide))
    fun t9 ⟨h9, f9, v9, r9, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shl_ok h9 (j := aTy) (by decide) (by decide)) fun t10 ⟨h10, f10, _, v10, _, r10⟩ => ?_
  rw [v9, Y8] at v10
  have T10 := (st2_shl_split v10 (wordsVal_lt _ _ _ _)).1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (st2_li1_ok t10) fun t11 ⟨⟨u11, m11⟩, r11⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have h11 : Ws t11 B Z w 63 := h10.of_keep r11
  refine WP.mono (shlC_ok h11 (j := aTy) (by decide) (by decide) (by rw [u11]; decide))
    fun t12 ⟨h12, f12, _, v12, _, r12⟩ => ?_
  rw [m11, T10, u11] at v12
  rw [m11] at f12
  have T12 := (st2_shl_split v12 (wordsVal_lt _ _ _ _)).1
  -- The comparison and the new remainder.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h12 (o := aDf) (a := aRm) (b := aTy) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t13 ⟨h13, f13, v13, b13, r13⟩ => ?_
  have R12 : num t12.mem B w aRm = num t8.mem B w aRm := by
    rw [f12.num (by decide) (by simp) (fit _ (by decide)), f10.num (by decide) (by simp) (fit _ (by decide)),
      f9.num (by decide) (by simp) (fit _ (by decide))]
  rw [R12] at v13
  have W13 := wsub_of_sub v13 (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _) b13
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (stBorrow_ok h13 (sl := sBb) (by decide) (by decide)) fun t14 ⟨h14, f14, s14, r14⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have aA : Ahead (arr w aRm) (arr w aDf) w := by
    simpa using ahead_of_ne (w := w) (o := aRm) (a := aDf) (by decide) 0 (by decide)
  refine WP.mono (sel_gen_ok h14 (o := aRm) (a := aDf) (b := aRm) (sl := sBb) (by decide) (by decide)
    (by decide) (by decide) aA (ahead_self _ _ _) (by decide) (by decide) (by rw [s14]; exact b13))
    fun t15 ⟨h15, f15, v15, r15⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (notBb_ok h15) fun t16 ⟨⟨u16, m16⟩, r16⟩ => ?_
  have h16 : Ws t16 B Z w 63 := h15.of_keep r16
  have sB15 : slot t15.mem B sBb = (t13.gpr .t4).toNat := by
    rw [f15.slot (by decide) (by simp), s14]
  have n16 : (t16.gpr .t4).toNat = 1 - (t13.gpr .t4).toNat := by
    rw [u16, xor_bits (by change slot t15.mem B sBb ≤ 1; rw [sB15]; exact b13) (by decide)]
    change (slot t15.mem B sBb + 1) % 2 = _
    rw [sB15]; omega
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shlC_ok h16 (j := aSy) (by decide) (by decide) (by rw [n16]; omega))
    fun t17 ⟨h17, f17, _, v17, _, r17⟩ => ?_
  rw [m16, n16] at v17
  rw [m16] at f17
  have Y17 := (st2_shl_split v17 (wordsVal_lt _ _ _ _)).1
  refine WP.mono (st2_next_ok t17) fun t ⟨⟨u18, m18⟩, r18⟩ => ?_
  rw [← m18] at f17 Y17
  have K17 : Keep [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .s9, .s10] s t17 := by
    have k := r1.mono (rs' := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .s9, .s10]) (by decide)
    have k := Keep.trans' k (r2.mono (by decide))
    have k := Keep.trans' k (r3.mono (by decide))
    have k := Keep.trans' k (r4.mono (by decide))
    have k := Keep.trans' k (r5.mono (by decide))
    have k := Keep.trans' k (r6.mono (by decide))
    have k := Keep.trans' k (r7.mono (by decide))
    have k := Keep.trans' k (r8.mono (by decide))
    have k := Keep.trans' k (r9.mono (by decide))
    have k := Keep.trans' k (r10.mono (by decide))
    have k := Keep.trans' k (r11.mono (by decide))
    have k := Keep.trans' k (r12.mono (by decide))
    have k := Keep.trans' k (r13.mono (by decide))
    have k := Keep.trans' k (r14.mono (by decide))
    have k := Keep.trans' k (r15.mono (by decide))
    have k := Keep.trans' k (r16.mono (by decide))
    have k := Keep.trans' k (r17.mono (by decide))
    exact k
  have mo : ∀ {js ds : List Nat} {m m' : Mem}, Frame B w js ds m m' →
      (∀ j ∈ js, j ∈ halves [wR] ++ [aRm, aSy, aTy, aDf]) → (∀ d ∈ ds, d ∈ [sBb]) →
      Frame B w (halves [wR] ++ [aRm, aSy, aTy, aDf]) [sBb] m m' := fun f hj hd => f.mono hj hd
  refine ⟨h17.of_keep r18, ?_, Keep.trans' (K17.mono (by decide)) (r18.mono (by decide)), ?_, ?_⟩
  · exact (((((((((((mo f2.toNarrow (by decide) (by decide)).trans (mo f4 (by decide) (by decide))).trans
      (mo f6.toNarrow (by decide) (by decide))).trans (mo f8 (by decide) (by decide))).trans
      (mo f9 (by decide) (by decide))).trans (mo f10 (by decide) (by decide))).trans
      (mo f12 (by decide) (by decide))).trans (mo f13 (by decide) (by decide))).trans
      (mo f14 (by decide) (by decide))).trans (mo f15 (by decide) (by decide))).trans
      (mo f17 (by decide) (by decide)))
  · rw [u18, K17.gpr (by decide)]
  · -- The values after each step.
    have mt : ∀ {js ds : List Nat} {m m' : Mem}, Frame B w js ds m m' →
        (∀ j ∈ js, j ∈ [aRm, aSy, aTy, aDf]) → (∀ d ∈ ds, d ∈ [sBb]) →
        Frame B w [aRm, aSy, aTy, aDf] [sBb] m m' := fun f hj hd => f.mono hj hd
    have g : Frame B w [aRm, aSy, aTy, aDf] [sBb] t8.mem t.mem :=
      (((((mt f9 (by decide) (by decide)).trans (mt f10 (by decide) (by decide))).trans
        (mt f12 (by decide) (by decide))).trans (mt f13 (by decide) (by decide))).trans
        (mt f14 (by decide) (by decide))).trans ((mt f15 (by decide) (by decide)).trans
          (mt f17 (by decide) (by decide)))
    have eX : num t.mem B (W2 w) wR = 2 * (2 * num s.mem B (W2 w) wR % 2 ^ (64 * W2 w)) % 2 ^ (64 * W2 w) := by
      rw [g.toWide.num (by decide) (by decide) (fW _ (by decide)),
        f8.toWide.num (by decide) (by simp) (fW _ (by decide)), X6.1]
    have Y15 : num t15.mem B w aSy = num s.mem B w aSy := by
      rw [f15.num (by decide) (by simp) (fit _ (by decide)), f14.num (by simp) (by decide) (fit _ (by decide)),
        f13.num (by decide) (by simp) (fit _ (by decide)), f12.num (by decide) (by simp) (fit _ (by decide)),
        f10.num (by decide) (by simp) (fit _ (by decide)), f9.num (by decide) (by simp) (fit _ (by decide)), Y8]
    rw [Y15] at Y17
    have eR : num t.mem B w aRm = if (t13.gpr .t4).toNat = 0 then wsub (64 * w) (num t8.mem B w aRm)
        (num t12.mem B w aTy) else num t8.mem B w aRm := by
      rw [f17.num (by decide) (by simp) (fit _ (by decide)), v15, s14,
        f14.num (j := aDf) (by simp) (by decide) (fit _ (by decide)),
        f14.num (j := aRm) (by simp) (by decide) (fit _ (by decide)), W13.1,
        f13.num (j := aRm) (by decide) (by simp) (fit _ (by decide)), R12]
    rw [eX, eR, Y17, sqrtStep_code (by omega) (wordsVal_lt _ _ _ _)]
    have er : num t8.mem B w aRm = (2 * ((2 * num s.mem B w aRm + 2 * num s.mem B (W2 w) wR / 2 ^ (64 * W2 w)) %
        2 ^ (64 * w)) + 2 * (2 * num s.mem B (W2 w) wR % 2 ^ (64 * W2 w)) / 2 ^ (64 * W2 w)) % 2 ^ (64 * w) := by
      rw [R8, R4, X2.2]
    have et : num t12.mem B w aTy = (2 * (2 * num s.mem B w aSy % 2 ^ (64 * w)) + 1) % 2 ^ (64 * w) := by
      rw [T12]; rfl
    have β := W13.2
    rw [← er, ← et]
    by_cases c : num t8.mem B w aRm < num t12.mem B w aTy
    · have b1 : (t13.gpr .t4).toNat = 1 := β.mpr c
      simp [c, b1]
    · have b0 : (t13.gpr .t4).toNat = 0 := by have := β.not.mpr c; omega
      simp [c, b0]

theorem st2_shl6_ofNat (a : Nat) : BitVec.ofNat 64 a <<< 6 = BitVec.ofNat 64 (64 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- The square root's state after `i` steps from `s0`. -/
structure SqI (s0 : State) (B : Addr) (Z w : Nat) (i : Nat) (t : State) : Prop where
  ws : Ws t B Z w 63
  keep : Frame B w (halves [wR] ++ [aRm, aSy, aTy, aDf]) [sBb] s0.mem t.mem
  regs : Keep st2Regs s0 t
  value : (num t.mem B (W2 w) wR, num t.mem B w aRm, num t.mem B w aSy) =
    (sqrtStep (64 * w) (64 * W2 w))^[i] (num s0.mem B (W2 w) wR, num s0.mem B w aRm, num s0.mem B w aSy)

theorem sqrt_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z (W2 w) 31) (hfit : arr w 63 ≤ Z)
    (hw : 0 < w) (hW : W2 w ≤ 1024) (hRm : num s.mem B w aRm = 0) (hSy : num s.mem B w aSy = 0)
    (hZ0 : num s.mem B w aZero = 0) :
    WP isa sqrt s fun t => Ws t B Z w 63 ∧
      Frame B w (halves [wR] ++ [aRm, aSy, aTy, aDf]) [sBb, sOk5] s.mem t.mem ∧ Keep st2Regs s t ∧
      num t.mem B w aRm = ((sqrtStep (64 * w) (64 * W2 w))^[64 * W2 w / 2]
        (num s.mem B (W2 w) wR, 0, 0)).2.1 ∧
      num t.mem B w aSy = ((sqrtStep (64 * w) (64 * W2 w))^[64 * W2 w / 2]
        (num s.mem B (W2 w) wR, 0, 0)).2.2 ∧
      slot t.mem B sOk5 = (if num t.mem B w aRm = 0 then 1 else 0) := by
  unfold sqrt
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxw_ok (N := 63) h hw hfit) fun t1 ⟨⟨h1, m1⟩, r1⟩ => ?_
  have fit : ∀ j < 63, arr w j + S w ≤ 2 ^ 64 := fun j hj => h1.fit64 hj
  have hle := h1.wle
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hc : WP isa (.block [.shift .sll .d .s7 .s9 6, .addi .s7 .s7 64]) t1 fun t =>
      (t.gpr .s7 = BitVec.ofNat 64 (64 * w + 64) ∧ t.mem = t1.mem) ∧ Keep [.s7] t1 t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h1.s9, st2_shl6_ofNat, exec_addi_nat (show 64 < 2048 by decide)]
    exact (BitVec.ofNat_add _ _).symm
  refine WP.mono hc fun t2 ⟨⟨c2, m2⟩, r2⟩ => ?_
  have h2 : Ws t2 B Z w 63 := h1.of_keep r2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have start : SqI t2 B Z w 0 t2 := ⟨h2, Frame.refl _ _ _ _ _, Keep.refl _ _, rfl⟩
  refine WP.mono (wp_countdown (body := sqrtBody) (cnt := .s7) (N := 64 * w + 64) (by omega_arith) (by omega)
    (SqI t2 B Z w) (fun i _ t inv _ => WP.mono (sqrtBody_ok inv.ws hW) fun u ⟨hu, fu, ru, cu, vu⟩ =>
      ⟨⟨hu, inv.keep.trans fu, Keep.trans' inv.regs ru, by
        rw [vu, inv.value, Function.iterate_succ_apply']⟩, cu⟩) start c2) fun t3 inv => ?_
  refine WP.mono (eqS_ok inv.ws (d := sOk5) (a := aRm) (b := aZero) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun t ⟨h4, f4, s4, r4⟩ => ?_
  have e2 : ∀ j < 63, num t2.mem B w j = num s.mem B w j := fun j _ => by rw [m2, m1]
  have eW : num t2.mem B (W2 w) wR = num s.mem B (W2 w) wR := by rw [m2, m1]
  have K : 64 * W2 w / 2 = 64 * w + 64 := by simp only [W2]; omega
  have V := inv.value
  rw [eW, e2 _ (by decide), e2 _ (by decide), hRm, hSy, ← K] at V
  have e4 : ∀ j < 63, num t.mem B w j = num t3.mem B w j := fun j hj => f4.num (by simp) (by decide) (fit _ hj)
  refine ⟨h4, ?_, ?_, ?_, ?_, ?_⟩
  · have f := inv.keep
    rw [m2, m1] at f
    exact (f.mono (by decide) (by decide)).trans (f4.mono (by simp) (by decide))
  · exact Keep.trans' (r1.mono (by decide)) (Keep.trans' (r2.mono (by decide)) (Keep.trans' inv.regs
      (r4.mono (by decide))))
  · rw [e4 _ (by decide), ← V]
  · rw [e4 _ (by decide), ← V]
  · have Z3 : num t3.mem B w aZero = 0 := by
      rw [inv.keep.num (by decide) (by decide) (fit _ (by decide)), e2 _ (by decide), hZ0]
    rw [s4, Z3, e4 _ (by decide)]

/-! ## The factors and the mask -/

theorem st2_xor1_toNat {x : BitVec 64} (hx : x.toNat ≤ 1) : (x ^^^ 1#64).toNat = 1 - x.toNat := by
  rw [xor_bits hx (by decide)]
  change (x.toNat + 1) % 2 = _
  omega

theorem st2_and_le1 {x y : BitVec 64} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    (x &&& y).toNat = x.toNat * y.toNat ∧ (x &&& y).toNat ≤ 1 := by
  rw [and01 hx hy]
  refine ⟨rfl, ?_⟩
  rcases (by omega : x.toNat = 0 ∨ x.toNat = 1) with e | e <;> rw [e] <;> omega

theorem maskOf_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N)
    (b0 : slot s.mem B sB0 ≤ 1) (b1 : slot s.mem B sB1 ≤ 1) (lt : slot s.mem B sLt ≤ 1)
    (ex : slot s.mem B sExact ≤ 1) (c1 : slot s.mem B sC1 ≤ 1) (c2 : slot s.mem B sC2 ≤ 1)
    (ok : slot s.mem B sOk5 ≤ 1) :
    WP isa (.block maskOf) s fun t => Ws t B Z w N ∧ Frame B w [] [sMask] s.mem t.mem ∧
      slot t.mem B sMask = (1 - slot s.mem B sB0) * (1 - slot s.mem B sB1) * slot s.mem B sLt *
        slot s.mem B sExact * (1 - slot s.mem B sC1) * (1 - slot s.mem B sC2) * slot s.mem B sOk5 ∧
      Keep opRegs s t := by
  have nw := h.nowrap
  have hz := h.hdr_le
  simp only [hdr_eq] at hz
  have hk : WP isa (.block maskOf) s fun u =>
      (u.mem = s.mem.writeW (off B sMask) ((((((((word s.mem B sB0 ^^^ 1#64) &&& (word s.mem B sB1 ^^^ 1#64)) &&&
        word s.mem B sLt) &&& word s.mem B sExact) &&& (word s.mem B sC1 ^^^ 1#64)) &&&
        (word s.mem B sC2 ^^^ 1#64)) &&& word s.mem B sOk5))) ∧ Keep [.t5, .t6] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [maskOf, h.s11, h.scr.st (d := sMask) (n := 8) (by simp only [sMask]; omega_arith),
      h.scr.al8 (d := sMask) (by simp only [sMask]; omega_arith) (by decide),
      h.scr.ld (d := sB0) (n := 8) (by simp only [sB0]; omega_arith),
      h.scr.al8 (d := sB0) (by simp only [sB0]; omega_arith) (by decide),
      h.scr.ld (d := sB1) (n := 8) (by simp only [sB1]; omega_arith),
      h.scr.al8 (d := sB1) (by simp only [sB1]; omega_arith) (by decide),
      h.scr.ld (d := sLt) (n := 8) (by simp only [sLt]; omega_arith),
      h.scr.al8 (d := sLt) (by simp only [sLt]; omega_arith) (by decide),
      h.scr.ld (d := sExact) (n := 8) (by simp only [sExact]; omega_arith),
      h.scr.al8 (d := sExact) (by simp only [sExact]; omega_arith) (by decide),
      h.scr.ld (d := sC1) (n := 8) (by simp only [sC1]; omega_arith),
      h.scr.al8 (d := sC1) (by simp only [sC1]; omega_arith) (by decide),
      h.scr.ld (d := sC2) (n := 8) (by simp only [sC2]; omega_arith),
      h.scr.al8 (d := sC2) (by simp only [sC2]; omega_arith) (by decide),
      h.scr.ld (d := sOk5) (n := 8) (by simp only [sOk5]; omega_arith),
      h.scr.al8 (d := sOk5) (by simp only [sOk5]; omega_arith) (by decide),
      show sB0 < 2048 by decide, show sB1 < 2048 by decide, show sLt < 2048 by decide,
      show sExact < 2048 by decide, show sC1 < 2048 by decide, show sC2 < 2048 by decide,
      show sOk5 < 2048 by decide, show sMask < 2048 by decide, add_ofNat_zero']
  refine WP.mono hk fun u ⟨mu, ku⟩ => ?_
  have sw := slot_write (m := s.mem) (B := B) (w := w) (d := sMask) ((((((((word s.mem B sB0 ^^^ 1#64) &&&
    (word s.mem B sB1 ^^^ 1#64)) &&& word s.mem B sLt) &&& word s.mem B sExact) &&& (word s.mem B sC1 ^^^ 1#64)) &&&
    (word s.mem B sC2 ^^^ 1#64)) &&& word s.mem B sOk5)) (by simp only [sMask]; omega_arith)
  rw [← mu] at sw
  refine ⟨h.of_keep ku, sw.1, ?_, ku.mono (by decide)⟩
  rw [sw.2]
  have x0 := st2_xor1_toNat (x := word s.mem B sB0) b0
  have x1 := st2_xor1_toNat (x := word s.mem B sB1) b1
  have x4 := st2_xor1_toNat (x := word s.mem B sC1) c1
  have x5 := st2_xor1_toNat (x := word s.mem B sC2) c2
  have a1 := st2_and_le1 (x := word s.mem B sB0 ^^^ 1#64) (y := word s.mem B sB1 ^^^ 1#64) (by rw [x0]; omega)
    (by rw [x1]; omega)
  have a2 := st2_and_le1 a1.2 lt
  have a3 := st2_and_le1 a2.2 ex
  have a4 := st2_and_le1 a3.2 (y := word s.mem B sC1 ^^^ 1#64) (by rw [x4]; omega)
  have a5 := st2_and_le1 a4.2 (y := word s.mem B sC2 ^^^ 1#64) (by rw [x5]; omega)
  have a6 := st2_and_le1 a5.2 ok
  rw [a6.1, a5.1, a4.1, a3.1, a2.1, a1.1, x0, x1, x4, x5]

theorem st2_li0_ok (s : State) :
    WP isa (.block [.li .t4 0]) s fun u => (u.gpr .t4 = 0 ∧ u.mem = s.mem) ∧ Keep [.t4] s u := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [fin64_exec_li_zero]

theorem factors_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w 63) (hZ0 : num s.mem B w aZero = 0)
    (b0 : slot s.mem B sB0 ≤ 1) (b1 : slot s.mem B sB1 ≤ 1) (lt : slot s.mem B sLt ≤ 1)
    (ex : slot s.mem B sExact ≤ 1) (c1 : slot s.mem B sC1 ≤ 1) (c2 : slot s.mem B sC2 ≤ 1)
    (ok : slot s.mem B sOk5 ≤ 1) :
    WP isa factors s fun t => Ws t B Z w 63 ∧ Frame B w [aP, aQ, aNy] [sMask] s.mem t.mem ∧
      Keep st2Regs s t ∧
      num t.mem B w aP = (num s.mem B w aD + num s.mem B w aSy) % 2 ^ (64 * w) / 2 ∧
      num t.mem B w aQ = wsub (64 * w) (num s.mem B w aD) (num s.mem B w aSy) / 2 ∧
      slot t.mem B sMask = (1 - slot s.mem B sB0) * (1 - slot s.mem B sB1) * slot s.mem B sLt *
        slot s.mem B sExact * (1 - slot s.mem B sC1) * (1 - slot s.mem B sC2) * slot s.mem B sOk5 := by
  have fit : ∀ j < 63, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  unfold factors
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (add_ok h (o := aP) (a := aD) (b := aSy) (z := aZero) (t := aNy) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hZ0) fun t1 ⟨h1, f1, v1, r1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (st2_li0_ok t1) fun t2 ⟨⟨u2, m2⟩, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (half_ok (h1.of_keep r2) (j := aP) (by decide) (by decide) (by rw [u2]; decide))
    fun t3 ⟨h3, f3, v3, _, r3⟩ => ?_
  rw [m2, u2, v1] at v3
  rw [m2] at f3
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h3 (o := aQ) (a := aD) (b := aSy) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t4 ⟨h4, f4, v4, b4, r4⟩ => ?_
  have e3 : ∀ j < 63, j ≠ aP → j ≠ aNy → num t3.mem B w j = num s.mem B w j := fun j hj h1' h2' => by
    rw [f3.num (by simpa using fun e => h1' e.symm) (by simp) (fit _ hj),
      f1.num (by simp; exact ⟨fun e => h2' e.symm, fun e => h1' e.symm⟩) (by simp) (fit _ hj)]
  rw [e3 _ (by decide) (by decide) (by decide), e3 _ (by decide) (by decide) (by decide)] at v4
  have Q4 := (wsub_of_sub v4 (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _) b4).1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (st2_li0_ok t4) fun t5 ⟨⟨u5, m5⟩, r5⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (half_ok (h4.of_keep r5) (j := aQ) (by decide) (by decide) (by rw [u5]; decide))
    fun t6 ⟨h6, f6, v6, _, r6⟩ => ?_
  rw [m5, u5, Q4] at v6
  rw [m5] at f6
  have fA : Frame B w [aP, aQ, aNy] [] s.mem t6.mem :=
    ((f1.mono (by decide) (by simp)).trans (f3.mono (by decide) (by simp))).trans
      ((f4.mono (by decide) (by simp)).trans (f6.mono (by decide) (by simp)))
  have sl : ∀ d, d + 8 ≤ hdr → slot t6.mem B d = slot s.mem B d := fun d hd => fA.slot hd (by simp)
  refine WP.mono (maskOf_ok h6 (by rw [sl _ (by decide)]; exact b0) (by rw [sl _ (by decide)]; exact b1)
    (by rw [sl _ (by decide)]; exact lt) (by rw [sl _ (by decide)]; exact ex) (by rw [sl _ (by decide)]; exact c1)
    (by rw [sl _ (by decide)]; exact c2) (by rw [sl _ (by decide)]; exact ok)) fun t ⟨h7, f7, s7, r7⟩ => ?_
  refine ⟨h7, (fA.mono (js' := [aP, aQ, aNy]) (ds' := [sMask]) (by decide) (by simp)).trans
    (f7.mono (by simp) (by decide)), ?_, ?_, ?_, ?_⟩
  · exact Keep.trans' (r1.mono (by decide)) (Keep.trans' (r2.mono (by decide)) (Keep.trans' (r3.mono (by decide))
      (Keep.trans' (r4.mono (by decide)) (Keep.trans' (r5.mono (by decide)) (Keep.trans' (r6.mono (by decide))
        (r7.mono (by decide)))))))
  · rw [f7.num (by simp) (by decide) (fit _ (by decide)), f6.num (by decide) (by simp) (fit _ (by decide)),
      f4.num (by decide) (by simp) (fit _ (by decide)), v3]
    simp
  · rw [f7.num (by simp) (by decide) (fit _ (by decide)), v6]
    simp
  · rw [s7, sl _ (by decide), sl _ (by decide), sl _ (by decide), sl _ (by decide), sl _ (by decide),
      sl _ (by decide), sl _ (by decide)]

end VG.Proof.Rsa.RISCV64.Keys
