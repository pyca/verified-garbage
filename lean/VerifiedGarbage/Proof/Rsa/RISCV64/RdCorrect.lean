module

public import VerifiedGarbage.Proof.Rsa.RISCV64.InvLaw
public import VerifiedGarbage.Proof.Rsa.RISCV64.RdLoad
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.RISCV64.RdStage2
import VerifiedGarbage.Proof.Rsa.RISCV64.RdSqrt
import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValInv
import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValFront
public import VerifiedGarbage.Proof.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.RecoverDetWords
import VerifiedGarbage.Proof.Rsa.RecoverRoot
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyWordDiv
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.RISCV64.RdOps
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Rsa.RISCV64.RdShift
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyDiv

/-! ### `Rsa.RISCV64.RdTwos`, which only this module used -/

section

/-!
# The halvings and the GCD of `vg_rsa_recover_primes_det` on RISC-V

* `twosInit_ok`, `twos_ok`: from `n` (narrow, `aN`) and `x = d e - 1`
  (wide, `wX`), the result of `64 w` steps of `RecoverDet.twoStep` with `b = 64 W` on
  `(u, x, 2^k x)` (`twosSt`: narrow `aU`, narrow `aX2`, wide `wX3`), from
  `(n - 1, x mod 2^(64 w), x)`, in closed form (`RecoverDet.twos_closed`): the
  trailing zeros of `u ∨ x` and of `u` (`RdShift`'s `tz_ok`), and shifts by
  them (`shrBy_ok`, `shlBy_ok`);
* `gcd_ok`: from `(x, u)`, `u` odd, `gcd(x, u)` by the batched GCD
  (`Proof/Rsa/RISCV64/IbInverse.lean`'s `gcd_ok`), 1 where `u = 1`, copied
  into the low half of the wide `wG`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (seqs sub3 sel bitOf stBorrow andS half copy sOdd sB sC)
open VG.Impl.Rsa.RISCV64.RecoverDet (gcd next aU aX2 aOne wG)
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Impl.Rsa.RISCV64.Keys (ptr mov)
open VG.Proof.Rsa.RISCV64.Loops (loopRegs Ahead out_step half64_arith)

/-- Index side conditions. -/
macro "rdidx" : tactic => `(tactic| ((try simp only [aU, aX2, aOne, wG, sOdd, sB, sC,
  Impl.Rsa.RISCV64.InvBatch.aX, Impl.Rsa.RISCV64.InvBatch.aMin, Impl.Rsa.RISCV64.InvBatch.aGcd,
  Impl.Rsa.RISCV64.InvBatch.aY, Impl.Rsa.RISCV64.RecoverDet.sU1,
  hdr_eq, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and,
  ne_eq]) <;> omega_arith))

/-! ## The GCD -/

open VG.Impl.Rsa.RISCV64.RecoverDet (sU1)

/-- The narrow arrays the GCD writes. -/
abbrev gcdArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 2 * wG]

/-- The registers the GCD changes. -/
abbrev gcdRegs : List Reg := .s8 :: InvBatch.invRegs

/-- `gcd`: from `(x, u)` (narrow `aX2`, `aU`), `u` odd, `gcd(x, u)` into the low
half of the wide `wG`, by the batched GCD (`InvLaw.gcd_ok`) and 1 where
`u = 1`. -/
theorem gcd_ok [InvLaw] {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N)
    (hN : 63 ≤ N) (hN' : N ≤ 256) (hw : 4 ≤ w) (h1 : num s.mem B w aOne = 1)
    (hodd : num s.mem B w aU % 2 = 1) :
    WP isa gcd s fun t => Ws t B Z w N ∧ Frame B w gcdArrs [sU1] s.mem t.mem ∧
      hiW t.mem B w wG = hiW s.mem B w wG ∧
      num t.mem B w (2 * wG) = Nat.gcd (num s.mem B w aX2) (num s.mem B w aU) ∧
      Keep gcdRegs s t := by
  have := h.wle
  have hS : S w = 8 * (w + 2) := rfl
  have nw := h.nowrap
  obtain fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  obtain fG : arr w (2 * wG) + 8 * w + 8 * (w + 2) ≤ 2 ^ 64 := by
    have := fit (2 * wG + 1) (by rdidx); have := arr_succ w (2 * wG); omega
  generalize hx : num s.mem B w aX2 = x at *
  generalize hu : num s.mem B w aU = u at *
  unfold gcd
  -- The inputs.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (o := Impl.Rsa.RISCV64.InvBatch.aX) (a := aX2) (by rdidx) (by rdidx) (by omega_using [hN'])
    (by rdidx)) fun t1 ⟨h1', k1, e1, r1, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h1' (o := Impl.Rsa.RISCV64.InvBatch.aMin) (a := aU) (by rdidx) (by rdidx) (by omega_using [hN'])
    (by rdidx)) fun t2 ⟨h2, k2, e2, r2, _⟩ => ?_
  rw [k1.num (by decide) (by simp) (fit _ (by rdidx)), hu] at e2
  rw [hx] at e1
  obtain e1' : num t2.mem B w Impl.Rsa.RISCV64.InvBatch.aX = x := by
    rw [k2.num (by decide) (by simp) (fit _ (by rdidx)), e1]
  -- `n = 2 w`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.keep [.s8] (Q := fun y => y.gpr .s8 = BitVec.ofNat 64 (2 * w) ∧ y.mem = t2.mem) ?_
    (by rfl) (by rfl)) fun t3 ⟨⟨s83, m3⟩, k3⟩ => ?_
  · brun [h2.s9]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using []
  obtain h3 := h2.of_keep k3
  obtain ctx : InvBatch.Ctx t3 B Z w N (2 * w) := ⟨h3, s83, by omega_using [hw], by omega_using [], by omega_using [hN], hw⟩
  -- The GCD.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (InvLaw.gcd_ok ctx hN' (x := x) (m := u) (by rw [m3]; exact e1')
    (by rw [← e1, show 32 * (2 * w) = 64 * w by omega_using []]; exact wordsVal_lt _ _ _ _) (by rw [m3]; exact e2)
    (by rw [← hu, show 32 * (2 * w) = 64 * w by omega_using []]; exact wordsVal_lt _ _ _ _)
    hodd) fun t4 ⟨h4, K4, k4, g4⟩ => ?_
  obtain u4 : num t4.mem B w Impl.Rsa.RISCV64.InvBatch.aMin = u := by
    rw [K4.num (by decide) (by simp) (fit _ (by rdidx)), m3, e2]
  obtain o4 : num t4.mem B w aOne = 1 := by
    rw [K4.num (by decide) (by simp) (fit _ (by rdidx)), m3, k2.num (by decide) (by simp) (fit _ (by rdidx)),
      k1.num (by decide) (by simp) (fit _ (by rdidx)), h1]
  -- 1 where `u = 1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h4 (d := sU1) (a := Impl.Rsa.RISCV64.InvBatch.aMin) (b := aOne) (by rdidx) (by rdidx)
    (by omega_using [hN']) (by rdidx) (by decide)) fun t5 ⟨h5, K5, v5, k5⟩ => ?_
  rw [u4, o4] at v5
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h5 (o := Impl.Rsa.RISCV64.InvBatch.aY) (a := Impl.Rsa.RISCV64.InvBatch.aGcd) (b := aOne)
    (sl := sU1) (by rdidx) (by rdidx) (by rdidx) (by omega_using [hN']) (by decide) (by rdidx) (by rdidx) (by decide)
    (by rw [v5]; split <;> decide)) fun t6 ⟨h6, K6, v6, k6⟩ => ?_
  -- Into `wG`.
  refine WP.mono (copy_ok h6 (o := 2 * wG) (a := Impl.Rsa.RISCV64.InvBatch.aY) (by rdidx) (by rdidx)
    (by omega_using [hN']) (by rdidx)) fun t ⟨h7, K7, v7, k7, o7⟩ => ?_
  obtain F6 : Frame B w (gcdArrs.take 12) [sU1] s.mem t6.mem :=
    (k1.mono (by decide) (by simp)).trans ((k2.mono (by decide) (by simp)).trans
      ((show Frame B w (gcdArrs.take 12) [sU1] t2.mem t3.mem by rw [m3]; exact Frame.refl _ _ _ _ _).trans
        ((K4.mono (by decide) (by simp)).trans ((K5.mono (by simp) (by simp)).trans (K6.mono (by decide) (by simp))))))
  refine ⟨h7, F6.join K7 (by simp) (by simp) (by simp) (by simp), ?_, ?_, ?_⟩
  · simp only [hiW]
    rw [o7.wordsVal (.inr (by omega_using [])) fG]
    refine F6.words (fun j hj => ?_) (fun e he => ?_) fG
    · have := (show ∀ j ∈ gcdArrs.take 12, j < 13 by decide) j hj
      have := arr_end (w := w) (show j < 2 * wG by unfold wG; omega_using [this])
      omega_using [this]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      have := hdr_le_arr w (2 * wG)
      simp only [sU1, hdr_eq] at *; omega_using [this]
  · rw [v7, v6, v5]
    by_cases e : u = 1
    · simp only [e, ↓reduceIte, Nat.one_ne_zero]
      rw [K5.num (by decide) (by simp [sU1, hdr_eq]) (fit _ (by rdidx)), o4, Nat.gcd_one_right]
    · simp only [e, ↓reduceIte]
      rw [K5.num (by decide) (by simp [sU1, hdr_eq]) (fit _ (by rdidx))]
      exact g4 (by omega_using [hodd, e])
  · exact Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (r1.mono (by decide))
      (r2.mono (by decide))) (k3.mono (by decide))) (k4.mono (by decide))) (k5.mono (by decide)))
      (k6.mono (by decide))) (k7.mono (by decide))

/-! ## The halvings -/

open VG.Impl.Rsa.RISCV64.RecoverDet (twosInit twos ctxW ctxw aN aOne aZero wX wX3)
open VG.Proof.Bignum.ShiftStages (tz tz_lt dvd_iff)

/-- Index side conditions of the halvings. -/
macro "twidx" : tactic => `(tactic| ((try simp only [aN, aOne, aZero, aU, aX2, wX, wX3,
  hdr_eq, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and,
  ne_eq]) <;> omega_arith))

/-- The registers the halvings and the GCD change. -/
abbrev rdRegs : List Reg := .s7 :: .s9 :: .s10 :: opRegs

/-- The halvings' state: `(u, x, 2^k x)`, narrow, narrow, wide. -/
def twosSt (m : Mem) (B : Addr) (w : Nat) : Nat × Nat × Nat :=
  (num m B w aU, num m B w aX2, num m B (W2 w) wX3)

theorem Frame.toNarrow1 {B : Addr} {w j : Nat} {ds : List Nat} {m m' : Mem}
    (h : Frame B (W2 w) [j] ds m m') : Frame B w [2 * j, 2 * j + 1] ds m m' := by
  simpa only [halves, List.flatMap_cons, List.flatMap_nil, List.append_nil] using h.toNarrow

theorem sub_eq_wsub {b x a c β : Nat} (e : x + c = a + 2 ^ b * β) (hx : x < 2 ^ b) (ha : a < 2 ^ b)
    (hc : c < 2 ^ b) (hβ : β ≤ 1) : x = VG.Proof.Rsa.RecoverDet.wsub b a c := by
  unfold VG.Proof.Rsa.RecoverDet.wsub
  rcases (show β = 0 ∨ β = 1 by omega_arith) with rfl | rfl
  · rw [show a + 2 ^ b - c = (a - c) + 2 ^ b by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

/-- `twosInit`, from the wide view: `2^k x := x`; `u := n - 1` and `x := x mod 2^(64 w)` (narrow);
the narrow view after. -/
theorem twosInit_ok {s : State} {B : Addr} {Z w N M : Nat} (h : Ws s B Z (W2 w) M)
    (hw : 0 < w) (hNZ : arr w N ≤ Z) (hN : 63 ≤ N) (hN' : N ≤ 2048) (hM : 20 ≤ M) (hMN : 2 * M ≤ N)
    (h1 : num s.mem B w aOne = 0) :
    WP isa twosInit s fun t => Ws t B Z w N ∧
      Frame B w [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2] [] s.mem t.mem ∧
      num t.mem B w aOne = 1 ∧
      twosSt t.mem B w = (VG.Proof.Rsa.RecoverDet.wsub (64 * w) (num s.mem B w aN) 1,
        num s.mem B (W2 w) wX % 2 ^ (64 * w), num s.mem B (W2 w) wX) ∧
      Keep rdRegs s t := by
  obtain hM' : M ≤ 2048 := by omega_arith
  obtain fXw := h.fit64 (j := wX) (by twidx)
  unfold twosInit
  -- 1: `2^k x := x` (wide).
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (by twidx) (by twidx) hM' (by twidx)) fun t1 ⟨h1', k1, e1, r1, _⟩ => ?_
  -- 2: the narrow view.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxw_ok h1' hw hNZ) fun t2 ⟨⟨h2, m2⟩, k2⟩ => ?_
  obtain fO := h2.fit64 (j := aOne) (by twidx)
  obtain fN := h2.fit64 (j := aN) (by twidx)
  obtain fX := h2.fit64 (j := 2 * wX) (by twidx)
  obtain fU := h2.fit64 (j := aU) (by twidx)
  have K1 := k1.toNarrow1
  -- 3: one.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (setOne_ok h2 (by twidx) hN') fun t3 ⟨h3, k3, e3, r3⟩ => ?_
  rw [m2, K1.num (by simp [aOne, wX3]) (by simp) fO, h1] at e3
  simp only [Nat.zero_div, Nat.mul_zero, Nat.add_zero] at e3
  -- 4: `u = n - 1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h3 (by twidx) (by twidx) (by twidx) hN' (by twidx) (by twidx))
    fun t4 ⟨h4, k4, e4, b4, r4⟩ => ?_
  rw [e3, k3.num (by simp [aOne, aN]) (by simp) fN, m2, K1.num (by simp [aN, wX3]) (by simp) fN] at e4
  obtain u4 : num t4.mem B w aU = VG.Proof.Rsa.RecoverDet.wsub (64 * w) (num s.mem B w aN) 1 :=
    sub_eq_wsub e4 (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _) (Nat.one_lt_two_pow (by omega_arith)) b4
  -- 5: `x` (narrow).
  refine WP.mono (copy_ok h4 (by twidx) (by twidx) hN' (by twidx)) fun t5 ⟨h5, k5, e5, r5, _⟩ => ?_
  rw [k4.num (by simp [aU, wX]) (by simp) fX, k3.num (by simp [aOne, wX]) (by simp) fX, m2,
    K1.num (by simp [wX, wX3]) (by simp) fX, num_low] at e5
  obtain fX3 := h1'.fit64 (j := wX3) (by twidx)
  refine ⟨h5, ?_, ?_, ?_, ?_⟩
  · have A := K1
    rw [← m2] at A
    exact (A.join k3 (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2]) (ds := [])).join
      (k4.join k5 (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2]) (ds := []))
      (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2]) (ds := [])
  · rw [k5.num (by simp [aOne, aX2]) (by simp) fO, k4.num (by simp [aOne, aU]) (by simp) fO, e3]
  · simp only [twosSt]
    rw [k5.num (by simp [aU, aX2]) (by simp) fU, u4, e5,
      k5.toWide.num (by decide) (by simp) fX3, k4.toWide.num (by decide) (by simp) fX3,
      k3.toWide.num (by decide) (by simp) fX3, m2, e1]
  · exact Keep.trans' (Keep.mono r1 (by decide)) (Keep.trans' (Keep.mono k2 (by decide))
      (Keep.trans' (Keep.mono r3 (by decide)) (Keep.trans' (Keep.mono r4 (by decide))
        (Keep.mono r5 (by decide)))))

/-- The registers the halvings change. -/
abbrev twosRegs : List Reg := .s8 :: .a2 :: .a3 :: .a5 :: .a6 :: .a7 :: rdRegs

/-- `twos`, from the wide view after `d e - 1`: `64 w` steps from `(n - 1, x mod 2^(64 w), x)`,
`n` narrow in `aN` and `x` wide in `wX`, in closed form (`RecoverDet.twos_closed`): the
trailing zeros of `u ∨ x` and of `u` (`ctz`), and shifts by them; the narrow view after. -/
theorem twos_ok {s : State} {B : Addr} {Z w N M : Nat} (h : Ws s B Z (W2 w) M)
    (hw : 2 ≤ w) (hNZ : arr w N ≤ Z) (hN : 63 ≤ N) (hN' : N ≤ 2048) (hM : 20 ≤ M)
    (hMN : 2 * M ≤ N) (hW : W2 w ≤ 1024) (h1 : num s.mem B w aOne = 0)
    (h0 : num s.mem B w aZero = 0) (hn1 : 1 ≤ num s.mem B w aN) (hn2 : num s.mem B w aN ≠ 1)
    {K : Nat} (hK : K ≤ 2 ^ 13) (hnb : num s.mem B w aN < 2 ^ K) :
    WP isa twos s fun t => Ws t B Z w N ∧
      Frame B w [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2] [] s.mem t.mem ∧
      num t.mem B w aOne = 1 ∧
      twosSt t.mem B w = (VG.Proof.Rsa.RecoverDet.twoStep (64 * W2 w))^[64 * w]
        (VG.Proof.Rsa.RecoverDet.wsub (64 * w) (num s.mem B w aN) 1,
          num s.mem B (W2 w) wX % 2 ^ (64 * w), num s.mem B (W2 w) wX) ∧
      Keep twosRegs s t := by
  obtain hM' : M ≤ 2048 := by omega_arith
  have hW2 : W2 w = 2 * w + 2 := rfl
  obtain fZs := h.fit64 (j := wX) (by twidx)
  unfold twos
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (twosInit_ok h (by omega_arith) hNZ hN hN' hM hMN h1) fun t0 ⟨h0', k0, o0, e0, r0⟩ => ?_
  simp only [twosSt, Prod.mk.injEq] at e0
  obtain ⟨eU, eX2, eX3⟩ := e0
  obtain fZ := h0'.fit64 (j := aZero) (by twidx)
  obtain fU := h0'.fit64 (j := aU) (by twidx)
  obtain fX := h0'.fit64 (j := aX2) (by twidx)
  obtain fO := h0'.fit64 (j := aOne) (by twidx)
  obtain z0 : num t0.mem B w aZero = 0 := by
    rw [k0.num (by simp [aZero, aOne, aU, aX2, wX3]) (by simp) fZ, h0]
  -- `u = n - 1`, nonzero and below `2^K` and `2^(64 w)`.
  obtain nlt : num s.mem B w aN < 2 ^ (64 * w) := wordsVal_lt _ _ _ _
  rw [VG.Proof.Rsa.RecoverDet.wsub_of_le nlt hn1] at eU ⊢
  generalize hUv : num s.mem B w aN - 1 = U at eU ⊢
  obtain hU0 : 0 < U := by omega_arith
  obtain hUk : U < 2 ^ (64 * w) := by omega_arith
  obtain hU13 : U < 2 ^ K := by omega_arith
  obtain tU : tz U < 2 ^ 13 := Nat.lt_of_lt_of_le (tz_lt hU0 hU13) hK
  obtain tUw : tz U < 64 * w := tz_lt hU0 hUk
  generalize hX2v : num t0.mem B w aX2 = X2 at eX2
  obtain tg : tz (Nat.gcd U X2) ≤ tz U :=
    (dvd_iff (show U ≠ 0 by omega_arith) _).mp (Nat.dvd_trans
      ((dvd_iff (Nat.gcd_ne_zero_left (show U ≠ 0 by omega_arith)) _).mpr (Nat.le_refl _)) (Nat.gcd_dvd_left U X2))
  -- 2: `s7 = tz (u ∨ x) = tz (gcd u x)`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (tz_ok (dst := .s7) h0' (A := aU) (Bx := aX2) (by twidx) (by twidx) hN' (by decide)
    (by
      change num t0.mem B w aU ||| num t0.mem B w aX2 ≠ 0
      rw [eU]; intro e; have := (Nat.or_eq_zero_iff.mp e).1; omega_arith))
    fun t1 ⟨m1, c1, k1⟩ => ?_
  change t1.gpr .s7 = BitVec.ofNat 64 (tz (num t0.mem B w aU ||| num t0.mem B w aX2)) at c1
  rw [eU, hX2v, VG.Proof.Rsa.RISCV64.Keys.tz_or_gcd (show U ≠ 0 by omega_arith)] at c1
  obtain h1' := h0'.of_keep k1
  -- 3: `s8 = tz u`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (tz_ok (dst := .s8) h1' (A := aU) (Bx := aZero) (by twidx) (by twidx) hN' (by decide)
    (by
      change num t1.mem B w aU ||| num t1.mem B w aZero ≠ 0
      rw [m1, eU]; intro e; have := (Nat.or_eq_zero_iff.mp e).1; omega_arith))
    fun t2 ⟨m2, c2, k2⟩ => ?_
  change t2.gpr .s8 = BitVec.ofNat 64 (tz (num t1.mem B w aU ||| num t1.mem B w aZero)) at c2
  rw [m1, eU, z0, Nat.or_zero] at c2
  obtain h2 := h1'.of_keep k2
  obtain c2' : t2.gpr .s7 = BitVec.ofNat 64 (tz (Nat.gcd U X2)) := by rw [k2.gpr (by decide)]; exact c1
  -- 4: `u := u / 2^(tz u)`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shrBy_ok h2 (X := aU) (r := tz U) (n := 7) (by twidx) hN' c2 (by decide) (by omega_arith) (by decide) hw (by omega_arith))
    fun t3 ⟨h3, f3, e3, k3⟩ => ?_
  -- 5: `x := x / 2^t`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shrBy_ok h3 (X := aX2) (r := tz (Nat.gcd U X2)) (by twidx) hN' (n := 7) (by rw [k3.gpr (by decide)]; exact c2') (by decide)
    (by omega_arith) (by decide) hw (by omega_arith)) fun t4 ⟨h4, f4, e4, k4⟩ => ?_
  -- 6: the wide view.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxW_ok h4 hW hMN) fun t5 ⟨⟨h5, m5⟩, k5⟩ => ?_
  -- 7: `2^k x := 2^k x 2^t` (wide).
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shlBy_ok h5 (X := wX3) (r := tz (Nat.gcd U X2)) (by twidx) hM'
    (n := 7) (by rw [k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide)]; exact c2')
    (by decide) (by omega_arith) (by decide) (by omega_arith) (by omega_arith)) fun t6 ⟨h6, f6, e6, k6⟩ => ?_
  -- 8: the narrow view.
  refine WP.mono (ctxw_ok h6 (by omega_arith) hNZ) fun t ⟨⟨h7, m7⟩, k7⟩ => ?_
  have F6 := f6.toNarrow1
  obtain fX3 := h0'.fit64 (j := 2 * wX3) (by twidx)
  obtain fX3w := h5.fit64 (j := wX3) (by twidx)
  rw [m2, m1] at f3
  rw [m5] at F6
  have e6' : num t6.mem B (W2 w) wX3 = num t5.mem B (W2 w) wX3 * 2 ^ tz (Nat.gcd U X2) % 2 ^ (64 * W2 w) := e6
  refine ⟨h7, ?_, ?_, ?_, ?_⟩
  · rw [m7]
    exact ((k0.join f3 (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2]) (ds := [])).join f4
      (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2]) (ds := [])).join F6
      (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2]) (ds := [])
  · rw [m7, F6.num (by simp [aOne, wX3]) (by simp) fO, f4.num (by simp [aOne, aX2]) (by simp) fO,
      f3.num (by simp [aOne, aU]) (by simp) fO, o0]
  · have x3l : num s.mem B (W2 w) wX < 2 ^ (64 * W2 w) := wordsVal_lt _ _ _ _
    rw [VG.Proof.Rsa.RecoverDet.twos_closed hU0 hUk x3l, ← eX2]
    simp only [twosSt, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [m7, F6.num (by simp [aU, wX3]) (by simp) fU, f4.num (by simp [aU, aX2]) (by simp) fU]
      have e3' : num t3.mem B w aU = num t2.mem B w aU / 2 ^ tz U := e3
      rw [e3', m2, m1, eU]
    · rw [m7, F6.num (by simp [aX2, wX3]) (by simp) fX]
      have e4' : num t4.mem B w aX2 = num t3.mem B w aX2 / 2 ^ tz (Nat.gcd U X2) := e4
      rw [e4', f3.num (by simp [aU, aX2]) (by simp) fX, hX2v]
    · change num t.mem B (W2 w) wX3 = _
      rw [m7]
      change num t6.mem B (W2 w) wX3 = _
      rw [e6', m5, f4.toWide.num (by decide) (by simp) fX3w, f3.toWide.num (by decide) (by simp) fX3w, eX3]
  · exact Keep.trans' (Keep.mono r0 (by decide)) (Keep.trans' (Keep.mono k1 (by decide))
      (Keep.trans' (Keep.mono k2 (by decide)) (Keep.trans' (Keep.mono k3 (by decide))
        (Keep.trans' (Keep.mono k4 (by decide)) (Keep.trans' (Keep.mono k5 (by decide))
          (Keep.trans' (Keep.mono k6 (by decide)) (Keep.mono k7 (by decide))))))))

end VG.Proof.Rsa.RISCV64.Keys

end

end

/-!
# `vg_rsa_recover_primes_det` on RISC-V: correctness

The second half of the function, after `d e - 1` (`RdLoad`'s `Dm`), as
`Proof/Rsa/RecoverDetModel.lean` models it: `stA_ok` runs the halvings, the
GCD and the first division (`St3`), `stB_ok` the second division, `b² - 4 n`,
the square root and the factors (`Det`), with the mask the model's
(`mask_eq`) and the code's quotient and remainder the model's where `m < n`
and the divisor is positive. `stores_ok`: the factors written under the mask
and the mask returned; `valid_ok`: a valid modulus, from the set-up to the
stores; `rd_correct`: the function, through `RecoverDet.model_correct_lt`, on
the registers and the stack (`fnPost`).
-/

-- separate module: its proofs (the stages chained, the stores and `rd_correct`) are not re-checked with
-- every change to the constant-time proof

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.RecDet

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Proof.Rsa.RecoverDet (deX okDE wsub wsub_of_le twoStep twosOut aOf ltOf m1Of dOf sqOf fourN xOf
  rootOf stage2 twos_iter prod_iter)
open VG.Impl.Rsa.RISCV64.Keys (seqs)
open VG.Spec.Rsa (isqrt)
open VG.Impl.Rsa.RISCV64.RecoverDet (twos gcd divA divB minus4n sqrt factors nArr aN aOne aZero aU aX2 aT
  aNeg1 aM1 aD aSy aTy aDf aP aQ aNy wZ wE wD wM wX wOne wX3 wA wR wN
  wDt wT2 wG wB wSq wDig wTmp wSD wSN sB0 sB1 sLt sExact sC1 sC2 sBb sOk5 sMask)
open VG.Impl.Rsa.RISCV64.Keys (sOdd sB sC)
open VG.Proof.Rsa.RISCV64.CrtValues (bit_ite bytes_in bytes_sep bytesAt_congr zeros_keep bytesAt_zero
  wordsVal_of_out)

/-- Index side conditions. `decide` first: it closes most of them as they stand, and the `simp only`
elaborates its sixty names at each of the proofs' two hundred uses. -/
macro "rdc" : tactic => `(tactic| first | decide | ((try simp only [nArr, nWide, aN, aOne, aZero, aU, aX2, aT,
  Impl.Rsa.RISCV64.RecoverDet.sU1, aNeg1, aM1, aD, aSy, aTy, aDf, aP, aQ, aNy, wZ, wE, wD, wM, wX, wOne,
  wX3, wA, wR, wN, wDt, wT2, wG, wB, wSq, wDig, wTmp, wSD, wSN, divSlots, sB0, sB1, sLt, sExact, sC1, sC2, sBb, sOk5,
  sMask, sOdd, sB, sC, halves, hdr_eq, List.flatMap_cons, List.flatMap_nil, List.cons_append,
  List.nil_append, List.append_nil, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
  and_true, true_and, ne_eq]) <;> first | decide | omega_arith))

/-! ## Zero arrays and the wide view -/

/-- A word of zero words is zero. -/
theorem word_zero_of {m : Mem} {B : Addr} {d K i : Nat} (h : wordsVal m B d K = 0) (hi : i < K) :
    word m B (d + 8 * i) = 0 := by
  have := wordsVal_zero_part (a := i) (c := 1) h (by omega_arith)
  simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at this
  exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)

/-- The narrow arrays `2 j` and `2 j + 1` zero: the wide array `j`'s upper half is. -/
theorem hiW_zero {m : Mem} {B : Addr} {w j : Nat} (h0 : wordsVal m B (arr w (2 * j)) (w + 2) = 0)
    (h1 : wordsVal m B (arr w (2 * j + 1)) (w + 2) = 0) : hiW m B w j = 0 := by
  rw [hiW_eq, wordsVal_zero_part (a := w) (c := 2) h0 (by omega_arith), num_zero h1]

/-- A wide number, past a frame of other narrow arrays. -/
theorem numW_of {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem} (f : Keys.Frame B w js ds m m') {j : Nat}
    (hj : ∀ k ∈ js, k / 2 ≠ j) (hd : ∀ d ∈ ds, d + 8 ≤ hdr) (fit : arr w (2 * j + 1) + S w ≤ 2 ^ 64) :
    num m' B (W2 w) j = num m B (W2 w) j :=
  f.toWide.num (fun k hk => by
      obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      exact hj k' hk') hd (by rw [arr_W2, S_W2]; have := arr_succ w (2 * j); omega_arith)

/-! ## The model -/

theorem twoStep_fst (b : Nat) (s : Nat × Nat × Nat) :
    (twoStep b s).1 = if s.1 % 2 = 0 then s.1 / 2 else s.1 := by
  unfold twoStep
  by_cases h1 : s.1 % 2 = 0
  · simp only [h1, ↓reduceIte]; split <;> rfl
  · simp only [h1, ↓reduceIte]

theorem twoStep_snd (b : Nat) (s : Nat × Nat × Nat) : (twoStep b s).2.1 ≤ s.2.1 := by
  unfold twoStep
  by_cases h1 : s.1 % 2 = 0
  · simp only [h1, ↓reduceIte]; split
    · exact Nat.div_le_self _ _
    · exact Nat.le_refl _
  · simp only [h1, ↓reduceIte, Nat.le_refl]

/-- The halvings' first part does not depend on the others. -/
theorem iter_fst (b k : Nat) (s : Nat × Nat × Nat) :
    ((twoStep b)^[k] s).1 = ((twoStep b)^[k] (s.1, 0, 0)).1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', twoStep_fst, twoStep_fst, ih]

theorem iter_snd (b k : Nat) (s : Nat × Nat × Nat) : ((twoStep b)^[k] s).2.1 ≤ s.2.1 := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => rw [Function.iterate_succ_apply']; exact Nat.le_trans (twoStep_snd _ _) ih

/-- What the GCD needs of the halvings' result: `u` odd and at most `n - 1`, `x` narrow. -/
theorem twos_out {nb wb n de : Nat} (three : 3 ≤ n) (hn : n < 2 ^ nb) :
    (twosOut nb wb n de).1 % 2 = 1 ∧ (twosOut nb wb n de).1 ≤ n - 1 ∧ (twosOut nb wb n de).2.1 < 2 ^ nb := by
  obtain un : wsub nb n 1 = n - 1 := wsub_of_le hn (by omega_arith)
  have ⟨o, l, _⟩ := twos_iter (b := wb) (N := n - 1) (x := 0) (k := nb) (by omega_arith) (by omega_arith)
    (Nat.two_pow_pos wb)
  unfold twosOut
  rw [iter_fst, un]
  exact ⟨o, l, Nat.lt_of_le_of_lt (iter_snd _ _ _) (Nat.mod_lt _ (Nat.two_pow_pos _))⟩

/-- `a`, the GCD times `2^k x`, as the code computes it. -/
theorem aOf_eq {nb wb n de : Nat} (hx3 : (twosOut nb wb n de).2.2 < 2 ^ wb)
    (hg : Nat.gcd (twosOut nb wb n de).1 (twosOut nb wb n de).2.1 < 2 ^ nb) :
    aOf nb wb n de = Nat.gcd (twosOut nb wb n de).2.1 (twosOut nb wb n de).1 * (twosOut nb wb n de).2.2 % 2 ^ wb := by
  unfold aOf
  rw [prod_iter _ _ _ hx3]
  simp only
  rw [Nat.mod_eq_of_lt hg, Nat.gcd_comm]

theorem ite_toNat (p : Prop) [Decidable p] : (if p then 1 else 0 : Nat) = (decide p).toNat := by
  by_cases h : p <;> simp [h]

theorem mask_bool (a b c d e f g : Bool) :
    (1 - a.toNat) * (1 - b.toNat) * c.toNat * d.toNat * (1 - e.toNat) * (1 - f.toNat) * g.toNat =
      (!(a || b) && c && (d && !(e || f) && g)).toNat := by
  revert a b c d e f g; decide

/-- The product of the checks' slots is the model's mask, the root's check the model's where `m < n` and
`b² > 4 n`. -/
theorem mask_eq {nb wb n de q rem B0 B1 Lt Ex C1 C2 Ok : Nat}
    (b0 : B0 = if de < 1 then 1 else 0) (b1 : B1 = if deX wb de < 1 then 1 else 0)
    (lt : Lt = if aOf nb wb n de / n < n then 1 else 0) (ex : Ex = if rem = 0 then 1 else 0)
    (c1 : C1 = if sqOf nb wb (RecoverDet.bOf nb q) < fourN wb n then 1 else 0)
    (c2 : C2 = if xOf nb wb n (RecoverDet.bOf nb q) < 1 then 1 else 0)
    (ok : ltOf nb wb n de = true → VG.Proof.Rsa.RecoverDet.ok4Of nb wb n (RecoverDet.bOf nb q) = true →
      Ok = if (rootOf nb wb n (RecoverDet.bOf nb q)).2.1 = 0 then 1 else 0) :
    (1 - B0) * (1 - B1) * Lt * Ex * (1 - C1) * (1 - C2) * Ok =
      (okDE wb de && ltOf nb wb n de && (stage2 nb wb n q rem).1).toNat := by
  subst b0 b1 lt ex c1 c2
  by_cases hl : ltOf nb wb n de = true
  · by_cases h4 : VG.Proof.Rsa.RecoverDet.ok4Of nb wb n (RecoverDet.bOf nb q) = true
    · rw [ok hl h4]
      simp only [ite_toNat]
      rw [mask_bool]
      rfl
    · have h4' := h4
      simp only [VG.Proof.Rsa.RecoverDet.ok4Of, Bool.or_eq_false_iff, not_and,
        decide_eq_false_iff_not, Classical.not_not, Bool.not_eq_eq_eq_not, Bool.not_true] at h4'
      obtain e : (stage2 nb wb n q rem).1 = false := by
        simp only [stage2, Bool.and_eq_false_iff]; exact .inl (.inr (by simpa using h4))
      rw [e, Bool.and_false]
      by_cases hc : sqOf nb wb (RecoverDet.bOf nb q) < fourN wb n
      · simp [hc]
      · have hx := h4' (by simpa using hc)
        simp [hx]
  · have hl' : ¬ aOf nb wb n de / n < n := fun c => hl (by simp [ltOf, RecoverDet.mOf, c])
    simp [hl', Bool.eq_false_iff.mpr hl]

/-! ## The halvings, the GCD and `a`, `m`, `r` -/

/-- The narrow arrays written by each stage. -/
abbrev u1 : List Nat := dmUsed ++ [22, 23, 41, 43, 44, 45]
abbrev u2 : List Nat := u1 ++ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 34]
abbrev u3 : List Nat := u2 ++ [28, 29, 24, 25, 26, 27, 30, 31, 10, 13]
abbrev u4 : List Nat := u3 ++ [51, 52, 53, 54, 55, 14, 15, 16, 17]
abbrev u5 : List Nat := u4 ++ [36, 37, 38, 39]
abbrev u6 : List Nat := u5 ++ [56, 57, 58, 59]

/-- After `a`, `m = ⌊a / n⌋` and `r = a mod n`, in the wide view. -/
structure St3 (s0 t : State) : Prop where
  cb : CB s0 s0.mem t
  ws : Ws t (bOf s0) (zOf s0) (WOf s0) 31
  n : num t.mem (bOf s0) (wOf s0) aN = Nv s0
  one : num t.mem (bOf s0) (wOf s0) aOne = 1
  oneW : num t.mem (bOf s0) (WOf s0) wOne = 1
  b0 : slot t.mem (bOf s0) sB0 = if deOf s0 < 1 then 1 else 0
  b1 : slot t.mem (bOf s0) sB1 = if deX (wbOf s0) (deOf s0) < 1 then 1 else 0
  nW : num t.mem (bOf s0) (WOf s0) wN = Nv s0
  m : num t.mem (bOf s0) (WOf s0) wDt = aOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) / Nv s0
  r : num t.mem (bOf s0) (WOf s0) wR = aOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) % Nv s0
  lt : slot t.mem (bOf s0) sLt = if aOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) / Nv s0 < Nv s0 then 1 else 0
  free : ∀ j < nArr, j ∉ u3 → wordsVal t.mem (bOf s0) (arr (wOf s0) j) (wOf s0 + 2) = 0

theorem stA_ok [InvLaw] {s0 s : State} (h : PreC s0) (three : 3 ≤ Nv s0)
    (hnT : 2 ^ (64 * (wOf s0 - 2)) ≤ Nv s0) (dm : Dm s0 s) :
    WP isa (seqs [twos, gcd, divA]) s (St3 s0) := by
  have ⟨b8, _, _, _, nk⟩ := bounds h
  have ⟨f1, f2⟩ := h.fits
  obtain fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  obtain wpos : 0 < wOf s0 := by simp only [wOf]; omega_arith
  have hk : kOf s0 ≤ 1024 := h.k2
  have hk1 : 64 ≤ kOf s0 := h.k1
  obtain hw5 : 5 ≤ wOf s0 := by rw [w_eq]; omega_arith
  obtain hw129 : wOf s0 ≤ 129 := by rw [w_eq]; omega_arith
  obtain hnl : Nv s0 < 2 ^ (64 * (wOf s0 - 1)) :=
    Nat.lt_of_lt_of_le nk (Nat.pow_le_pow_right (by decide) (by rw [w_eq]; omega_arith))
  -- The halvings.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (twos_ok (N := nArr) dm.ws (by omega_using [hw5]) f1 (by decide) (by decide) (by decide) (by decide) f2
    (num_zero (dm.free _ (by rdc) (by rdc))) (num_zero (dm.free _ (by rdc) (by rdc)))
    (by rw [dm.n]; omega_using [three]) (by rw [dm.n]; omega_using [three])
    (K := 8 * kOf s0) (by omega_arith) (by rw [dm.n]; exact nk))
    fun t1 ⟨w1, F1, one1, st1, k1⟩ => ?_
  obtain c1 := dm.cb.step w1 F1 (by rdc) (by rdc) k1
  obtain fr1 := free_step (U' := u1) F1 (by rdc) fit (by rdc) (by rdc) dm.free
  obtain n1 : num t1.mem (bOf s0) (wOf s0) aN = Nv s0 := by rw [F1.num (by rdc) (by rdc) (fit _ (by rdc)), dm.n]
  obtain tw : twosSt t1.mem (bOf s0) (wOf s0) = twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) := by
    rw [st1, dm.n, dm.x]; rfl
  obtain ⟨uo, ul, x2l⟩ := twos_out (wb := wbOf s0) (de := deOf s0) three (show Nv s0 < 2 ^ nbOf s0 by omega_arith)
  obtain u1v : num t1.mem (bOf s0) (wOf s0) aU = (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).1 := by
    rw [← tw]; rfl
  obtain x21 : num t1.mem (bOf s0) (wOf s0) aX2 = (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).2.1 := by
    rw [← tw]; rfl
  obtain x31 : num t1.mem (bOf s0) (WOf s0) wX3 = (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).2.2 := by
    rw [← tw]; rfl
  -- The GCD.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  obtain hw4 : 4 ≤ wOf s0 := by omega_using [hw5]
  refine WP.mono (gcd_ok w1 (by decide) (by decide) hw4 one1 (by rw [u1v]; exact uo))
    fun t2 ⟨w2, F2, hi2, g2, k2⟩ => ?_
  obtain c2 := c1.step w2 F2 (by rdc) (by rdc) k2
  obtain fr2 := free_step (U' := u2) F2 (by rdc) fit (by rdc) (by rdc) fr1
  obtain n2 : num t2.mem (bOf s0) (wOf s0) aN = Nv s0 := by rw [F2.num (by rdc) (by rdc) (fit _ (by rdc)), n1]
  obtain G : num t2.mem (bOf s0) (WOf s0) wG =
      Nat.gcd (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).2.1 (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).1 := by
    rw [numW_low (by rw [hi2]; exact hiW_zero (fr1 _ (by rdc) (by rdc)) (fr1 _ (by rdc) (by rdc))),
      g2, x21, u1v]
  obtain X3 : num t2.mem (bOf s0) (WOf s0) wX3 = (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).2.2 := by
    rw [numW_of F2 (by rdc) (by rdc) (fit _ (by rdc)), x31]
  obtain aof : aOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) =
      num t2.mem (bOf s0) (WOf s0) wG * num t2.mem (bOf s0) (WOf s0) wX3 % 2 ^ (64 * WOf s0) := by
    rw [G, X3]
    refine aOf_eq (by rw [← x31]; exact wordsVal_lt _ _ _ _) ?_
    have := Nat.gcd_le_left (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).2.1
      (show 0 < (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).1 by omega_arith)
    omega_arith
  -- `a`, `m` and `r`.
  refine WP.mono (divA_ok (show Ws t2 (bOf s0) (zOf s0) (wOf s0) 63 from w2) f2 hw5 (by omega_using [hw129])
    (hiW_zero (fr2 _ (by rdc) (by rdc)) (fr2 _ (by rdc) (by rdc)))
    (num_zero (wide_zero (fr2 _ (by rdc) (by rdc)) (fr2 _ (by rdc) (by rdc))))
    (num_zero (wide_zero (fr2 _ (by rdc) (by rdc)) (fr2 _ (by rdc) (by rdc))))
    (words_low (w := WOf s0 + 2) (v := WOf s0 + 1) (by omega_using []) (wide_zero (fr2 _ (by rdc) (by rdc)) (fr2 _ (by rdc) (by rdc)))
      (Nat.two_pow_pos _))
    (by rw [n2]; exact hnT) (by rw [n2]; exact hnl)) fun t3 ⟨w3, F3, k3, vN, vA, vR, vLt⟩ => ?_
  obtain c3 := c2.step w2 F3 (by rdc) (by rdc) k3
  obtain fr3 := free_step (U' := u3) F3 (by rdc) fit (by rdc) (by rdc) fr2
  refine ⟨c3, w3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fr3⟩
  · rw [F3.num (by rdc) (by rdc) (fit _ (by rdc)), n2]
  · rw [F3.num (by rdc) (by rdc) (fit _ (by rdc)), F2.num (by rdc) (by rdc) (fit _ (by rdc)), one1]
  · rw [numW_of F3 (by rdc) (by rdc) (fit _ (by rdc)), numW_of F2 (by rdc) (by rdc) (fit _ (by rdc)),
      numW_of F1 (by rdc) (by rdc) (fit _ (by rdc)), dm.one]
  · rw [F3.slot (by rdc) (by rdc), F2.slot (by rdc) (by rdc), F1.slot (by rdc) (by rdc), dm.b0]
  · rw [F3.slot (by rdc) (by rdc), F2.slot (by rdc) (by rdc), F1.slot (by rdc) (by rdc), dm.b1]
  · rw [vN, n2]
  · rw [vA, ← aof, n2]
  · rw [vR, ← aof, n2]
  · rw [vLt, ← aof, n2]

/-! ## The second division, `b² - 4 n`, the square root and the factors -/

/-- After the factors, in the narrow view: the mask and the factors the model's,
with the code's quotient `q` and remainder `rem` where the divisor is positive. -/
structure Det (s0 : State) (q rem : Nat) (t : State) : Prop where
  cb : CB s0 s0.mem t
  ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr
  div : ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) = true → 0 < m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) →
    q = dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) / m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) ∧
    rem = dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) % m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)
  mask : slot t.mem (bOf s0) sMask = (okDE (wbOf s0) (deOf s0) && ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) &&
    (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).1).toNat
  p : (okDE (wbOf s0) (deOf s0) && ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) &&
    (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).1) = true →
    num t.mem (bOf s0) (wOf s0) aP = (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).2.1
  q : (okDE (wbOf s0) (deOf s0) && ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) &&
    (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).1) = true →
    num t.mem (bOf s0) (wOf s0) aQ = (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).2.2

theorem stB_ok {s0 s : State} (h : PreC s0) (three : 3 ≤ Nv s0) (st : St3 s0 s) :
    WP isa (seqs [divB, minus4n, sqrt, factors]) s fun t => ∃ q rem, Det s0 q rem t := by
  have ⟨b8, _, bw, bwe, _⟩ := bounds h
  have ⟨f1, f2⟩ := h.fits
  obtain fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  obtain wpos : 0 < wOf s0 := by simp only [wOf]; omega_arith
  -- `m + 1`, `n - r`, their quotient and whether it is exact.
  have hk2 : kOf s0 ≤ 1024 := h.k2
  have hk1 : 64 ≤ kOf s0 := h.k1
  obtain hw5 : 5 ≤ wOf s0 := by rw [w_eq]; omega_arith
  obtain hw129 : wOf s0 ≤ 129 := by rw [w_eq]; omega_arith
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (divB_ok st.ws f1 f2 hw5 hw129 (num_zero (st.free _ (by rdc) (by rdc))) st.one)
    fun t4 ⟨w4, F4, k4, neg4, ex4l, dv4⟩ => ?_
  obtain c4 := st.cb.step w4 F4 (by rdc) (by rdc) k4
  obtain fr4 := free_step (U' := u4) F4 (by rdc) fit (by rdc) (by rdc) st.free
  have ⟨_, _, _, _, nk⟩ := bounds h
  obtain hnl : Nv s0 < 2 ^ (64 * (wOf s0 - 1)) :=
    Nat.lt_of_lt_of_le nk (Nat.pow_le_pow_right (by decide) (by rw [w_eq]; omega_arith))
  obtain pn : 2 ^ (64 * (wOf s0 - 1)) ≤ 2 ^ nbOf s0 :=
    Nat.pow_le_pow_right (by decide) (by show 64 * (wOf s0 - 1) ≤ 64 * wOf s0; omega_using [])
  obtain nlb : Nv s0 < 2 ^ nbOf s0 := Nat.lt_of_lt_of_le hnl pn
  obtain n0 : 0 < Nv s0 := by omega_using [three]
  -- Where `m < n`: the model's divisor `m + 1` and dividend `n - r`.
  obtain hlt : ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) = true →
      num t4.mem (bOf s0) (wOf s0) aD =
        dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) / m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) ∧
      slot t4.mem (bOf s0) sExact = if dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) %
        m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) = 0 then 1 else 0 := by
    intro hl
    obtain hm : aOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) / Nv s0 < Nv s0 := of_decide_eq_true hl
    obtain hr : aOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) % Nv s0 < Nv s0 := Nat.mod_lt _ n0
    obtain e1 : m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) =
        aOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) / Nv s0 + 1 := by
      unfold m1Of RecoverDet.mOf
      rw [Nat.mod_eq_of_lt (Nat.lt_trans hm nlb), Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hm) nlb)]
    obtain e2 : dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) =
        Nv s0 - aOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) % Nv s0 := by
      unfold dOf RecoverDet.rOf
      rw [Nat.mod_eq_of_lt (Nat.lt_trans hr nlb), wsub_of_le nlb (Nat.le_of_lt hr)]
    rw [e1, e2]
    have := dv4 (by rw [st.m, st.n]; exact hm) (by rw [st.r, st.n]; exact hr) (by rw [st.n]; exact hnl)
    rwa [st.m, st.r, st.n] at this
  -- The remainder: the model's where `m < n`, else as the slot says.
  generalize hrem : (if ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) = true then
    dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) % m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)
    else 1 - slot t4.mem (bOf s0) sExact) = rem
  obtain ex4 : slot t4.mem (bOf s0) sExact = if rem = 0 then 1 else 0 := by
    rw [← hrem]
    by_cases hl : ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) = true
    · rw [ite_eq_left hl]; exact (hlt hl).2
    · rw [ite_eq_right hl]; split <;> omega_arith
  obtain hdiv : ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) = true → 0 < m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) →
      num t4.mem (bOf s0) (wOf s0) aD =
        dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) / m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) ∧
      rem = dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) % m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) :=
    fun hl _ => ⟨(hlt hl).1, by rw [← hrem, ite_eq_left hl]⟩
  -- `b`, `b²`, `4 n` and `b² - 4 n`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (minus4n_ok w4 f2 neg4 (hiW_zero (fr4 _ (by rdc) (by rdc)) (fr4 _ (by rdc) (by rdc)))
    (num_zero (wide_zero (fr4 _ (by rdc) (by rdc)) (fr4 _ (by rdc) (by rdc))))
    (by rw [numW_of F4 (by rdc) (by rdc) (fit _ (by rdc)), st.oneW]))
    fun t5 ⟨w5, F5, k5, d5, sq5, n5, r5, c15, c25⟩ => ?_
  obtain c5 := c4.step w4 F5 (by rdc) (by rdc) k5
  obtain fr5 := free_step (U' := u5) F5 (by rdc) fit (by rdc) (by rdc) fr4
  have b5 : num t5.mem (bOf s0) (wOf s0) aD =
      RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD) := d5
  obtain bl : RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD) < 2 ^ nbOf s0 :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain sqv : num t5.mem (bOf s0) (WOf s0) wSq =
      sqOf (nbOf s0) (wbOf s0) (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD)) := by
    rw [sq5, b5, sqOf_eq bl (by omega_arith)]
  obtain nWv : num t4.mem (bOf s0) (WOf s0) wN = Nv s0 := by
    rw [numW_of F4 (by rdc) (by rdc) (fit _ (by rdc)), st.nW]
  obtain fN : num t5.mem (bOf s0) (WOf s0) wN = fourN (wbOf s0) (Nv s0) := by rw [n5, nWv]
  obtain xv : num t5.mem (bOf s0) (WOf s0) wR =
      xOf (nbOf s0) (wbOf s0) (Nv s0) (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD)) := by
    rw [r5, sqv, fN]; rfl
  -- The square root.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sqrt_ok w5 f1 (by omega_using [wpos]) hw129 (num_zero (fr5 _ (by rdc) (by rdc))))
    fun t6 ⟨w6, F6, k6, sy6, ok6⟩ => ?_
  obtain c6 := c5.step w4 F6 (by rdc) (by rdc) k6
  obtain fr6 := free_step (U' := u6) F6 (by rdc) fit (by rdc) (by rdc) fr5
  generalize hX : xOf (nbOf s0) (wbOf s0) (Nv s0) (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD)) = X
    at xv
  obtain syv : num t6.mem (bOf s0) (wOf s0) aSy = isqrt X % 2 ^ nbOf s0 := by rw [sy6, xv]
  obtain rt : ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) = true →
      VG.Proof.Rsa.RecoverDet.ok4Of (nbOf s0) (wbOf s0) (Nv s0)
        (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD)) = true →
      (rootOf (nbOf s0) (wbOf s0) (Nv s0) (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD))).2.2 =
        isqrt X ∧
      ((rootOf (nbOf s0) (wbOf s0) (Nv s0) (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD))).2.1 = 0 ↔
        isqrt X * isqrt X = X) ∧ isqrt X < 2 ^ nbOf s0 := fun hl h4 => by
    rw [← hX]; exact VG.Proof.Rsa.RecoverDet.root_bridge three b8 bw bwe hl (hlt hl).1 h4
  obtain d6 : num t6.mem (bOf s0) (wOf s0) aD = RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD) := by
    rw [F6.num (by rdc) (by rdc) (fit _ (by rdc)), b5]
  -- The checks' slots.
  obtain b0 : slot t6.mem (bOf s0) sB0 = if deOf s0 < 1 then 1 else 0 := by
    rw [F6.slot (by rdc) (by rdc), F5.slot (by rdc) (by rdc), F4.slot (by rdc) (by rdc), st.b0]
  obtain b1 : slot t6.mem (bOf s0) sB1 = if deX (wbOf s0) (deOf s0) < 1 then 1 else 0 := by
    rw [F6.slot (by rdc) (by rdc), F5.slot (by rdc) (by rdc), F4.slot (by rdc) (by rdc), st.b1]
  obtain lt : slot t6.mem (bOf s0) sLt =
      if aOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) / Nv s0 < Nv s0 then 1 else 0 := by
    rw [F6.slot (by rdc) (by rdc), F5.slot (by rdc) (by rdc), F4.slot (by rdc) (by rdc), st.lt]
  obtain ex : slot t6.mem (bOf s0) sExact = if rem = 0 then 1 else 0 := by
    rw [F6.slot (by rdc) (by rdc), F5.slot (by rdc) (by rdc), ex4]
  obtain c1 : slot t6.mem (bOf s0) sC1 = if sqOf (nbOf s0) (wbOf s0)
      (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD)) < fourN (wbOf s0) (Nv s0) then 1 else 0 := by
    rw [F6.slot (by rdc) (by rdc), c15, sqv, fN]
  obtain c2 : slot t6.mem (bOf s0) sC2 = if xOf (nbOf s0) (wbOf s0) (Nv s0)
      (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD)) < 1 then 1 else 0 := by
    rw [F6.slot (by rdc) (by rdc), c25, xv, hX]
  obtain ok : slot t6.mem (bOf s0) sOk5 = if isqrt X * isqrt X = X then 1 else 0 := by rw [ok6, xv]
  obtain okm : ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) = true →
      VG.Proof.Rsa.RecoverDet.ok4Of (nbOf s0) (wbOf s0) (Nv s0)
        (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD)) = true →
      slot t6.mem (bOf s0) sOk5 = if (rootOf (nbOf s0) (wbOf s0) (Nv s0)
        (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD))).2.1 = 0 then 1 else 0 := fun hl h4 => by
    rw [ok]; exact if_congr (rt hl h4).2.1.symm rfl rfl
  -- The factors.
  refine WP.mono (factors_ok w6 (num_zero (fr6 _ (by rdc) (by rdc))) (by rw [b0]; exact bit_ite)
    (by rw [b1]; exact bit_ite) (by rw [lt]; exact bit_ite) (by rw [ex]; exact bit_ite)
    (by rw [c1]; exact bit_ite) (by rw [c2]; exact bit_ite) (by rw [ok]; exact bit_ite))
    fun t7 ⟨w7, F7, k7, p7, q7, mk7⟩ => ?_
  obtain c7 := c6.step w6 F7 (by rdc) (by rdc) k7
  obtain mk := mask_eq b0 b1 lt ex c1 c2 okm
  -- Under the mask, `m < n` and `b² > 4 n`, so the root is the model's.
  obtain ry : (okDE (wbOf s0) (deOf s0) && ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) &&
      (stage2 (nbOf s0) (wbOf s0) (Nv s0) (num t4.mem (bOf s0) (wOf s0) aD) rem).1) = true →
      isqrt X % 2 ^ nbOf s0 =
        (rootOf (nbOf s0) (wbOf s0) (Nv s0) (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD))).2.2 :=
    fun hb => by
      simp only [stage2, Bool.and_eq_true] at hb
      obtain r := rt hb.1.2 hb.2.1.2
      rw [r.1, Nat.mod_eq_of_lt r.2.2]
  exact ⟨_, _, c7, w7, hdiv, by rw [mk7]; exact mk, fun hb => by rw [p7, d6, syv, ry hb]; rfl,
    fun hb => by rw [q7, d6, syv, ry hb]; rfl⟩

/-! ## The stores -/

theorem rdMask_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (bit : slot s.mem B sMask ≤ 1) :
    WP isa (.block VG.Impl.Rsa.RISCV64.RecoverDet.mask) s fun t =>
      (t.gpr .t4 = (if decide (slot s.mem B sMask ≠ 0) then BitVec.allOnes 64 else 0) ∧ t.mem = s.mem) ∧
        Keep [.t4, .t5] s t := by
  have hz := h.hdr_le
  have nw := h.nowrap
  refine WP.keep _ ?_ (by rfl) (by rfl)
  obtain hz' : sMask + 8 ≤ Z := by simp only [hdr_eq, sMask] at hz ⊢; omega_arith
  brun [VG.Impl.Rsa.RISCV64.RecoverDet.mask, h.s11, fin64_exec_li_zero, add_ofNat_zero',
    h.scr.al8 (d := sMask) (by omega_arith) (by decide), h.scr.ld (d := sMask) (n := 8) hz',
    show sMask < 2048 by decide]
  exact mask_of_slot _ bit

/-- The outputs, as the function leaves them. -/
structure Out (s0 : State) (b : Bool) (P Q : Nat) (u : State) : Prop where
  ce : CE s0 u
  p : Spec.Rsa.bytesAt u.mem (s0.gpr .a0) (kOf s0) =
    if b then Spec.Rsa.i2osp (P % 256 ^ kOf s0) (kOf s0) else List.replicate (kOf s0) 0
  q : Spec.Rsa.bytesAt u.mem (s0.gpr .a2) (kOf s0) =
    if b then Spec.Rsa.i2osp (Q % 256 ^ kOf s0) (kOf s0) else List.replicate (kOf s0) 0
  a0 : (u.gpr .a0).toNat = b.toNat

theorem stores_ok {s0 t : State} (h : PreC s0) (c : CB s0 s0.mem t) (ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr)
    {b : Bool} {P Q : Nat} (hm : slot t.mem (bOf s0) sMask = b.toNat)
    (hp : num t.mem (bOf s0) (wOf s0) aP = P) (hq : num t.mem (bOf s0) (wOf s0) aQ = Q) :
    WP isa VG.Impl.Rsa.RISCV64.RecoverDet.stores t (Out s0 b P Q) := by
  have hz := h.zk
  have hk1 : 64 ≤ kOf s0 := h.k1
  have hk2 : kOf s0 ≤ 1024 := h.k2
  obtain lw : kOf s0 ≤ 8 * wOf s0 := by simp only [wOf]; omega_arith
  obtain bit : slot t.mem (bOf s0) sMask ≤ 1 := by rw [hm]; exact Bool.toNat_le b
  obtain Z64 : zOf s0 ≤ 2 ^ 64 := by have := h.ws; simp only [zOf]; omega_arith
  obtain fitZ : ∀ j < nArr, arr (wOf s0) j + 8 * wOf s0 ≤ zOf s0 := fun j hj => by
    have := Nat.le_trans (arr_end hj) h.fits.1; simp only [S] at this; omega_arith
  obtain wp : (s0.gpr .a0).toNat + kOf s0 ≤ 2 ^ 64 := by have := h.wp; rw [h.h1] at this; exact this
  obtain wq : (s0.gpr .a2).toNat + kOf s0 ≤ 2 ^ 64 := by have := h.wq; rw [h.h3] at this; exact this
  obtain pw : (⟨s0.gpr .a0, kOf s0⟩ : Region) ∈ s0.wr := by rw [← h.pR_eq, h.hwr]; simp
  obtain qw : (⟨s0.gpr .a2, kOf s0⟩ : Region) ∈ s0.wr := by rw [← h.qR_eq, h.hwr]; simp
  obtain ps : (⟨s0.gpr .a0, kOf s0⟩ : Region).Disjoint (sR s0) := by rw [← h.pR_eq]; exact h.ps
  obtain qs : (⟨s0.gpr .a2, kOf s0⟩ : Region).Disjoint (sR s0) := by rw [← h.qR_eq]; exact h.qs
  obtain p_q : (⟨s0.gpr .a0, kOf s0⟩ : Region).Disjoint ⟨s0.gpr .a2, kOf s0⟩ := by
    rw [← h.pR_eq, ← h.qR_eq]; exact h.pq
  obtain db : decide (slot t.mem (bOf s0) sMask ≠ 0) = b := by rw [hm]; cases b <;> rfl
  unfold VG.Impl.Rsa.RISCV64.RecoverDet.stores
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (rdMask_ok ws bit) fun t1 ⟨⟨m4, m1⟩, k1⟩ => ?_
  obtain ws1 := ws.of_keep k1
  obtain c1 := c.of_keep k1 m1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (storeBytes_ok ws1 (j := aP) (by decide) (by decide) c1.s3
    (by rw [c1.s2, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by decide) (by decide) (by decide) m4
    (by omega_arith) lw (fun i hi => by rw [c1.wr]; exact bytes_in pw (by omega_arith) i hi)
    (bytes_sep ps (by omega_arith)) wp) fun t2 ⟨ws2, b2, o2, k2⟩ => ?_
  obtain c2 := c1.of_out k2 o2 ps (by omega_arith)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (storeBytes_ok ws2 (j := aQ) (b := decide (slot t.mem (bOf s0) sMask ≠ 0)) (by decide)
    (by decide) c2.s4 (by rw [c2.s2, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by decide) (by decide)
    (by decide) (by rw [k2.gpr (by decide)]; exact m4) (by omega_arith) lw
    (fun i hi => by rw [c2.wr]; exact bytes_in qw (by omega_arith) i hi) (bytes_sep qs (by omega_arith)) wq)
    fun t3 ⟨ws3, b3, o3, k3⟩ => ?_
  obtain c3 := c2.of_out k3 o3 qs (by omega_arith)
  have hz3 := ws3.hdr_le
  have nw3 := ws3.nowrap
  obtain hM : sMask + 8 ≤ zOf s0 := by simp only [hdr_eq, sMask] at hz3 ⊢; omega_arith
  obtain hb : WP isa (.block [.load .d .a0 .s11 sMask]) t3 fun u =>
      (u.gpr .a0 = word t3.mem (bOf s0) sMask ∧ u.mem = t3.mem) ∧ Keep [.a0] t3 u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [ws3.s11, add_ofNat_zero', ws3.scr.al8 (d := sMask) (by omega_arith) (by decide),
      ws3.scr.ld (d := sMask) (n := 8) hM, show sMask < 2048 by decide]
  refine WP.mono hb fun u ⟨⟨ua, um⟩, ku⟩ => ?_
  obtain W1 : ∀ {m : Mem} {d : Nat}, wordsVal m (bOf s0) d 1 = (word m (bOf s0) d).toNat := by
    intro m d; simp [wordsVal]
  obtain qv : num t2.mem (bOf s0) (wOf s0) aQ = num t.mem (bOf s0) (wOf s0) aQ :=
    (wordsVal_of_out (d := arr (wOf s0) aQ) (k := wOf s0) ps o2 (fitZ _ (by decide)) Z64).trans (by rw [m1])
  obtain sM : slot t3.mem (bOf s0) sMask = slot t.mem (bOf s0) sMask := by
    obtain e := wordsVal_of_out (d := sMask) (k := 1) qs o3 (by omega_arith) Z64
    obtain e2 := wordsVal_of_out (d := sMask) (k := 1) ps o2 (by omega_arith) Z64
    rw [W1, W1] at e e2
    change (word t3.mem (bOf s0) sMask).toNat = (word t.mem (bOf s0) sMask).toNat
    rw [e, e2, m1]
  refine ⟨⟨(ku.gpr (by decide)).trans c3.s11, (ku.gpr (by decide)).trans c3.ra, ku.2.1.trans c3.rd,
    ku.2.2.trans c3.wr, fun i hi => by rw [um]; exact c3.hdr i hi⟩, ?_, ?_, ?_⟩
  · rw [um, bytesAt_congr fun c hc => zeros_keep p_q (by omega_arith) o3 hc]
    cases b
    · exact bytesAt_zero fun c hc => by rw [b2 c hc, db]; rfl
    · rw [bytes_of_store (m := t1.mem) (B := bOf s0) (w := wOf s0) (j := aP) lw
        (fun c hc => by rw [b2 c hc, db]; rfl), m1, hp]; rfl
  · rw [um]
    cases b
    · exact bytesAt_zero fun c hc => by rw [b3 c hc, db]; rfl
    · rw [bytes_of_store (m := t2.mem) (B := bOf s0) (w := wOf s0) (j := aQ) lw
        (fun c hc => by rw [b3 c hc, db]; rfl), qv, hq]; rfl
  · rw [ua]
    change slot t3.mem (bOf s0) sMask = _
    rw [sM, hm]

/-! ## A valid modulus -/

/-- The outputs of a valid modulus, with the code's quotient and remainder. -/
def VP (s0 u : State) : Prop :=
  ∃ q rem P Q, (ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) = true → 0 < m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) →
      q = dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) / m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) ∧
      rem = dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) % m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)) ∧
    ((okDE (wbOf s0) (deOf s0) && ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) &&
      (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).1) = true →
      P = (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).2.1 ∧ Q = (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).2.2) ∧
    Out s0 (okDE (wbOf s0) (deOf s0) && ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) &&
      (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).1) P Q u

/-- A valid modulus is odd and at least 3. -/
theorem nv_facts {s0 : State} (hmv : Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true) :
    Nv s0 % 2 = 1 ∧ 3 ≤ Nv s0 := by
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hmv
  obtain ⟨⟨⟨o, b⟩, _⟩, _⟩ := hmv
  exact ⟨o, Nat.le_trans (show 3 ≤ 2 ^ 2 by decide) (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by decide)) b)⟩

/-- A valid modulus's top word, word `w - 2`, is not zero: its first octet is not. -/
theorem nv_top {s0 : State} (hmv : Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true) (hk : 1 ≤ kOf s0) :
    2 ^ (64 * (wOf s0 - 2)) ≤ Nv s0 := by
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hmv
  obtain ⟨_, b⟩ := hmv
  refine Nat.le_trans ?_ b
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by rw [w_eq]; omega)

theorem valid_ok [InvLaw] {s0 s : State} (h : PreC s0) (hmv : Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true)
    (c : CB s0 s0.mem s) : WP isa VG.Impl.Rsa.RISCV64.RecoverDet.valid s (VP s0) := by
  obtain three := (nv_facts hmv).2
  unfold VG.Impl.Rsa.RISCV64.RecoverDet.valid
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (setup_ok h c) fun t1 ⟨c1, w1, z1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok h c1 w1 z1) fun t2 l2 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (prod_ok h l2) fun t3 p3 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  unfold VG.Impl.Rsa.RISCV64.RecoverDet.det
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (deMinus_ok h p3) fun t4 d4 => ?_
  rw [show [twos, gcd, divA, divB, minus4n, sqrt, factors] =
    [twos, gcd, divA] ++ [divB, minus4n, sqrt, factors] from rfl, wp_seqs_append (by simp) (by simp)]
  refine WP.mono (stA_ok h three (nv_top hmv (Nat.le_trans (by decide : 1 ≤ 64) h.k1)) d4) fun t5 s5 => ?_
  refine WP.mono (stB_ok h three s5) fun t6 ⟨q, rem, d6⟩ => ?_
  exact WP.mono (stores_ok h d6.cb d6.ws d6.mask rfl rfl) fun u o =>
    ⟨q, rem, _, _, d6.div, fun hb => ⟨d6.p hb, d6.q hb⟩, o⟩

/-! ## The function -/

theorem bytesAt_length (m : Mem) (p : Addr) (L : Nat) : (Spec.Rsa.bytesAt m p L).length = L := by
  simp [Spec.Rsa.bytesAt]

/-- `primesKeyDet` of the initial state's bytes. -/
theorem pkd_eq (s0 : State) : Spec.Rsa.primesKeyDet (nB s0) (eB s0) (dB s0) =
    if Spec.Rsa.modulusValid (Nv s0) (kOf s0) then
      (Spec.Rsa.recoverDet (Nv s0) (Ev s0) (Dv s0)).map fun (p, q) =>
        (Spec.Rsa.i2osp p (kOf s0), Spec.Rsa.i2osp q (kOf s0))
    else none := by
  unfold Spec.Rsa.primesKeyDet
  rw [bytesAt_length]

theorem post_valid {s0 u v : State} (h : PreC s0) (hmv : Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true)
    (vp : VP s0 u) (hm : v.mem = u.mem) (ha : v.gpr .a0 = u.gpr .a0) : fnPost s0 v := by
  obtain ⟨q, rem, P, Q, hdiv, hPQ, o⟩ := vp
  have ⟨b8, bde, bw, bwe, nk⟩ := bounds h
  have ⟨odd, three⟩ := nv_facts hmv
  obtain mc := VG.Proof.Rsa.RecoverDet.model_correct_lt (nb := nbOf s0) (wb := wbOf s0) (e := Ev s0) (d := Dv s0)
    (q := q) (rem := rem) odd three b8 bde bw bwe hdiv
  unfold VG.Proof.Rsa.RecoverDet.result at mc
  generalize (okDE (wbOf s0) (deOf s0) && ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) &&
    (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).1) = b at o mc hPQ
  replace mc : (if b = true then some (P, Q) else none) = Spec.Rsa.recoverDet (Nv s0) (Ev s0) (Dv s0) := by
    cases b
    · exact mc
    · rw [(hPQ rfl).1, (hPQ rfl).2]; exact mc
  unfold fnPost
  rw [pkd_eq]
  simp only [hmv, ↓reduceIte]
  rw [← mc]
  obtain e8 : (256 : Nat) ^ kOf s0 = 2 ^ (8 * kOf s0) := by rw [Nat.pow_mul]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none, Spec.Rsa.writtenAll, hm]
    refine ⟨?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, ha, o.a0]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rw [o.p, o.q]
      simp
  · simp only [↓reduceIte] at mc
    obtain pq := VG.Proof.Rsa.RecoverDet.recoverDet_mul mc.symm
    obtain P1 : 1 ≤ P := by
      rcases Nat.eq_zero_or_pos P with h0 | h0
      · rw [h0, Nat.zero_mul] at pq; omega_arith
      · exact h0
    obtain Q1 : 1 ≤ Q := by
      rcases Nat.eq_zero_or_pos Q with h0 | h0
      · rw [h0, Nat.mul_zero] at pq; omega_arith
      · exact h0
    obtain hP : P < 256 ^ kOf s0 := by
      rw [e8]; have := Nat.le_mul_of_pos_right P Q1; omega_arith
    obtain hQ : Q < 256 ^ kOf s0 := by
      rw [e8]; have := Nat.le_mul_of_pos_left Q P1; omega_arith
    simp only [↓reduceIte, Option.map_some, Spec.Rsa.writtenAll, List.map_cons, List.map_nil, hm]
    refine ⟨?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, ha, o.a0]; rfl
    · rw [o.p, o.q]
      simp only [↓reduceIte, Nat.mod_eq_of_lt hP, Nat.mod_eq_of_lt hQ]

theorem post_fail {s0 u v : State} (hv : ¬ Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true)
    (hw : Spec.Rsa.writtenAll u.mem (outs s0) ((u.gpr .a0).setWidth 32) none) (hm : v.mem = u.mem)
    (ha : v.gpr .a0 = u.gpr .a0) : fnPost s0 v := by
  unfold fnPost
  rw [Bool.not_eq_true] at hv
  rw [pkd_eq]
  simp only [hv, Bool.false_eq_true, ↓reduceIte]
  rw [hm, ha]
  exact hw

theorem rd_correct [InvLaw] (s : State) (hpre : (Spec.Rsa.recoverPrimesDetContract RISCV64.abi).pre s) :
    ∃ tr t, Exec isa VG.Impl.Rsa.RISCV64.RecoverDet.code s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  show WP isa VG.Impl.Rsa.RISCV64.RecoverDet.code s fun t => abiPreserved s t ∧ fnPost s t
  obtain h := preC_of hpre
  refine WP.mono (WP.rdwr (Q := fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra ∧
    fnPost s t) ?_) fun t ⟨⟨hp, hra, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  unfold VG.Impl.Rsa.RISCV64.RecoverDet.code
  rw [WP.seq_iff]
  refine WP.mono (entry_ok h) fun e c => ?_
  rw [WP.seq_iff]
  refine WP.mono (nCheck_ok h c) fun t ⟨t0, tm, kt⟩ => ?_
  obtain ct := c.of_keep kt tm
  rw [WP.seq_iff]
  refine WP.ite _ (Steps.eval_zero t .s0) (fun hz => ?_) (fun hz => ?_)
  · have hz' : t.gpr .s0 = 0 := by simpa using hz
    obtain hv := t0.mp hz'
    refine WP.mono (valid_ok h hv ct) fun u vp => ?_
    obtain ⟨_, _, _, _, _, _, o⟩ := id vp
    exact WP.mono (restore_ok' h o.ce) fun v ⟨vp', vra, vm, va⟩ => ⟨vp', vra, post_valid h hv vp vm va⟩
  · have hz' : t.gpr .s0 ≠ 0 := by simpa using hz
    obtain hv : ¬ Spec.Rsa.modulusValid (Nv s) (kOf s) = true := fun e => hz' (t0.mpr e)
    refine WP.mono (fail_ok h ct) fun u ⟨ce, hw⟩ => ?_
    exact WP.mono (restore_ok' h ce) fun v ⟨vp', vra, vm, va⟩ => ⟨vp', vra, post_fail hv hw vm va⟩

end VG.Proof.Rsa.RISCV64.RecDet
