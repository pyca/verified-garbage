module

public import VerifiedGarbage.Proof.Rsa.RISCV64.RdOps
public import VerifiedGarbage.Proof.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public import VerifiedGarbage.Proof.Rsa.KeyMath
public import VerifiedGarbage.Proof.Rsa.RISCV64.InvLaw
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Rsa.RISCV64.RdShift
import VerifiedGarbage.Proof.Rsa.RecoverDetWords
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyDiv
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

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
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have fG : arr w (2 * wG) + 8 * w + 8 * (w + 2) ≤ 2 ^ 64 := by
    have := fit (2 * wG + 1) (by rdidx); have := arr_succ w (2 * wG); omega
  generalize hx : num s.mem B w aX2 = x at *
  generalize hu : num s.mem B w aU = u at *
  unfold gcd
  -- The inputs.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (o := Impl.Rsa.RISCV64.InvBatch.aX) (a := aX2) (by rdidx) (by rdidx) (by omega)
    (by rdidx)) fun t1 ⟨h1', k1, e1, r1, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h1' (o := Impl.Rsa.RISCV64.InvBatch.aMin) (a := aU) (by rdidx) (by rdidx) (by omega)
    (by rdidx)) fun t2 ⟨h2, k2, e2, r2, _⟩ => ?_
  rw [k1.num (by decide) (by simp) (fit _ (by rdidx)), hu] at e2
  rw [hx] at e1
  have e1' : num t2.mem B w Impl.Rsa.RISCV64.InvBatch.aX = x := by
    rw [k2.num (by decide) (by simp) (fit _ (by rdidx)), e1]
  -- `n = 2 w`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.keep [.s8] (Q := fun y => y.gpr .s8 = BitVec.ofNat 64 (2 * w) ∧ y.mem = t2.mem) ?_
    (by rfl) (by rfl)) fun t3 ⟨⟨s83, m3⟩, k3⟩ => ?_
  · brun [h2.s9]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have h3 := h2.of_keep k3
  have ctx : InvBatch.Ctx t3 B Z w N (2 * w) := ⟨h3, s83, by omega, by omega, by omega, hw⟩
  -- The GCD.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (InvLaw.gcd_ok ctx hN' (x := x) (m := u) (by rw [m3]; exact e1')
    (by rw [← e1, show 32 * (2 * w) = 64 * w by omega]; exact wordsVal_lt _ _ _ _) (by rw [m3]; exact e2)
    (by rw [← hu, show 32 * (2 * w) = 64 * w by omega]; exact wordsVal_lt _ _ _ _)
    hodd) fun t4 ⟨h4, K4, k4, g4⟩ => ?_
  have u4 : num t4.mem B w Impl.Rsa.RISCV64.InvBatch.aMin = u := by
    rw [K4.num (by decide) (by simp) (fit _ (by rdidx)), m3, e2]
  have o4 : num t4.mem B w aOne = 1 := by
    rw [K4.num (by decide) (by simp) (fit _ (by rdidx)), m3, k2.num (by decide) (by simp) (fit _ (by rdidx)),
      k1.num (by decide) (by simp) (fit _ (by rdidx)), h1]
  -- 1 where `u = 1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h4 (d := sU1) (a := Impl.Rsa.RISCV64.InvBatch.aMin) (b := aOne) (by rdidx) (by rdidx)
    (by omega) (by rdidx) (by decide)) fun t5 ⟨h5, K5, v5, k5⟩ => ?_
  rw [u4, o4] at v5
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h5 (o := Impl.Rsa.RISCV64.InvBatch.aY) (a := Impl.Rsa.RISCV64.InvBatch.aGcd) (b := aOne)
    (sl := sU1) (by rdidx) (by rdidx) (by rdidx) (by omega) (by decide) (by rdidx) (by rdidx) (by decide)
    (by rw [v5]; split <;> decide)) fun t6 ⟨h6, K6, v6, k6⟩ => ?_
  -- Into `wG`.
  refine WP.mono (copy_ok h6 (o := 2 * wG) (a := Impl.Rsa.RISCV64.InvBatch.aY) (by rdidx) (by rdidx)
    (by omega) (by rdidx)) fun t ⟨h7, K7, v7, k7, o7⟩ => ?_
  have F6 : Frame B w (gcdArrs.take 12) [sU1] s.mem t6.mem :=
    (k1.mono (by decide) (by simp)).trans ((k2.mono (by decide) (by simp)).trans
      ((show Frame B w (gcdArrs.take 12) [sU1] t2.mem t3.mem by rw [m3]; exact Frame.refl _ _ _ _ _).trans
        ((K4.mono (by decide) (by simp)).trans ((K5.mono (by simp) (by simp)).trans (K6.mono (by decide) (by simp))))))
  refine ⟨h7, F6.join K7 (by simp) (by simp) (by simp) (by simp), ?_, ?_, ?_⟩
  · simp only [hiW]
    rw [o7.wordsVal (.inr (by omega)) fG]
    refine F6.words (fun j hj => ?_) (fun e he => ?_) fG
    · have := (show ∀ j ∈ gcdArrs.take 12, j < 13 by decide) j hj
      have := arr_end (w := w) (show j < 2 * wG by unfold wG; omega)
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      have := hdr_le_arr w (2 * wG)
      simp only [sU1, hdr_eq] at *; omega
  · rw [v7, v6, v5]
    by_cases e : u = 1
    · simp only [e, ↓reduceIte, Nat.one_ne_zero]
      rw [K5.num (by decide) (by simp [sU1, hdr_eq]) (fit _ (by rdidx)), o4, Nat.gcd_one_right]
    · simp only [e, ↓reduceIte]
      rw [K5.num (by decide) (by simp [sU1, hdr_eq]) (fit _ (by rdidx))]
      exact g4 (by omega)
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
  have hM' : M ≤ 2048 := by omega_arith
  have fXw := h.fit64 (j := wX) (by twidx)
  unfold twosInit
  -- 1: `2^k x := x` (wide).
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (by twidx) (by twidx) hM' (by twidx)) fun t1 ⟨h1', k1, e1, r1, _⟩ => ?_
  -- 2: the narrow view.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxw_ok h1' hw hNZ) fun t2 ⟨⟨h2, m2⟩, k2⟩ => ?_
  have fO := h2.fit64 (j := aOne) (by twidx)
  have fN := h2.fit64 (j := aN) (by twidx)
  have fX := h2.fit64 (j := 2 * wX) (by twidx)
  have fU := h2.fit64 (j := aU) (by twidx)
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
  have u4 : num t4.mem B w aU = VG.Proof.Rsa.RecoverDet.wsub (64 * w) (num s.mem B w aN) 1 :=
    sub_eq_wsub e4 (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _) (Nat.one_lt_two_pow (by omega_arith)) b4
  -- 5: `x` (narrow).
  refine WP.mono (copy_ok h4 (by twidx) (by twidx) hN' (by twidx)) fun t5 ⟨h5, k5, e5, r5, _⟩ => ?_
  rw [k4.num (by simp [aU, wX]) (by simp) fX, k3.num (by simp [aOne, wX]) (by simp) fX, m2,
    K1.num (by simp [wX, wX3]) (by simp) fX, num_low] at e5
  have fX3 := h1'.fit64 (j := wX3) (by twidx)
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
  have hM' : M ≤ 2048 := by omega_arith
  have hW2 : W2 w = 2 * w + 2 := rfl
  have fZs := h.fit64 (j := wX) (by twidx)
  unfold twos
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (twosInit_ok h (by omega_arith) hNZ hN hN' hM hMN h1) fun t0 ⟨h0', k0, o0, e0, r0⟩ => ?_
  simp only [twosSt, Prod.mk.injEq] at e0
  obtain ⟨eU, eX2, eX3⟩ := e0
  have fZ := h0'.fit64 (j := aZero) (by twidx)
  have fU := h0'.fit64 (j := aU) (by twidx)
  have fX := h0'.fit64 (j := aX2) (by twidx)
  have fO := h0'.fit64 (j := aOne) (by twidx)
  have z0 : num t0.mem B w aZero = 0 := by
    rw [k0.num (by simp [aZero, aOne, aU, aX2, wX3]) (by simp) fZ, h0]
  -- `u = n - 1`, nonzero and below `2^K` and `2^(64 w)`.
  have nlt : num s.mem B w aN < 2 ^ (64 * w) := wordsVal_lt _ _ _ _
  rw [VG.Proof.Rsa.RecoverDet.wsub_of_le nlt hn1] at eU ⊢
  generalize hUv : num s.mem B w aN - 1 = U at eU ⊢
  have hU0 : 0 < U := by omega_arith
  have hUk : U < 2 ^ (64 * w) := by omega_arith
  have hU13 : U < 2 ^ K := by omega_arith
  have tU : tz U < 2 ^ 13 := Nat.lt_of_lt_of_le (tz_lt hU0 hU13) hK
  have tUw : tz U < 64 * w := tz_lt hU0 hUk
  generalize hX2v : num t0.mem B w aX2 = X2 at eX2
  have tg : tz (Nat.gcd U X2) ≤ tz U :=
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
  have h1' := h0'.of_keep k1
  -- 3: `s8 = tz u`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (tz_ok (dst := .s8) h1' (A := aU) (Bx := aZero) (by twidx) (by twidx) hN' (by decide)
    (by
      change num t1.mem B w aU ||| num t1.mem B w aZero ≠ 0
      rw [m1, eU]; intro e; have := (Nat.or_eq_zero_iff.mp e).1; omega_arith))
    fun t2 ⟨m2, c2, k2⟩ => ?_
  change t2.gpr .s8 = BitVec.ofNat 64 (tz (num t1.mem B w aU ||| num t1.mem B w aZero)) at c2
  rw [m1, eU, z0, Nat.or_zero] at c2
  have h2 := h1'.of_keep k2
  have c2' : t2.gpr .s7 = BitVec.ofNat 64 (tz (Nat.gcd U X2)) := by rw [k2.gpr (by decide)]; exact c1
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
  have fX3 := h0'.fit64 (j := 2 * wX3) (by twidx)
  have fX3w := h5.fit64 (j := wX3) (by twidx)
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
