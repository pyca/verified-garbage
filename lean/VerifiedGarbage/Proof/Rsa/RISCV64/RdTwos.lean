module

public import VerifiedGarbage.Proof.Rsa.RISCV64.RdOps
public import VerifiedGarbage.Proof.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public import VerifiedGarbage.Proof.Rsa.KeyMath
public import VerifiedGarbage.Proof.Rsa.RISCV64.InvLaw
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyDiv
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The halvings and the GCD of `vg_rsa_recover_primes_det` on RISC-V

* `twosInit_ok`, `twosBody_ok`, `twos_ok`: from `n` (narrow, `aN`) and `x = d e - 1`
  (wide, `wX`), the result of `64 w` steps of `RecoverDet.twoStep` with `b = 64 W` on
  `(u, x, 2^k x)` (`twosSt`: narrow `aU`, narrow `aX2`, wide `wX3`), from
  `(n - 1, x mod 2^(64 w), x)`; eight actual steps suffice when the public
  low byte of `n - 1` is nonzero, as the remaining steps are identities;
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

/-- A word of a masked selection, `x ⊕ ((h ⊕ x) ∧ mask)`. -/
theorem xsel64 (x h : BitVec 64) (b : Bool) :
    x ^^^ ((h ^^^ x) &&& (if b then BitVec.allOnes 64 else 0)) = if b then h else x := by
  rw [BitVec.xor_comm]; exact select64_arith x h b

theorem shlk_ofNat (a k : Nat) : BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (2 ^ k * a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_comm,
    Nat.mul_mod_mod]

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

open VG.Impl.Rsa.RISCV64.RecoverDet (halfIfBody dblIf dblIfBody)
open VG.Impl.Rsa.RISCV64.RecoverDet (twosInit twosFlags halfIf twosBody twos ctxW ctxw aN aOne aT wX wX3 wT2
  sU sX sEven sBoth)

/-- The tail of `twosFlags`: `even := ¬u₀` and `both := ¬x₀ ∧ ¬u₀`, from the slots `sU`, `sX`. -/
theorem flagsTail_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) :
    WP isa (.block [.load .d .t5 .s11 sU, .load .d .t6 .s11 sX, .logicImm .xor .t5 .t5 1,
        .logicImm .xor .t6 .t6 1, .store .d .t5 .s11 sEven, .logic .and .t6 .t6 .t5, .store .d .t6 .s11 sBoth]) s
      fun u => (u.mem = (s.mem.writeW (off B sEven) (word s.mem B sU ^^^ 1#64)).writeW (off B sBoth)
        ((word s.mem B sX ^^^ 1#64) &&& (word s.mem B sU ^^^ 1#64))) ∧ Keep [.t5, .t6] s u := by
  have nw := h.nowrap
  have hz := h.hdr_le
  simp only [hdr_eq] at hz
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h.s11, h.scr.st (d := sEven) (n := 8) (by simp only [sEven]; omega_arith),
    h.scr.al8 (d := sEven) (by simp only [sEven]; omega_arith) (by decide),
    h.scr.st (d := sBoth) (n := 8) (by simp only [sBoth]; omega_arith),
    h.scr.al8 (d := sBoth) (by simp only [sBoth]; omega_arith) (by decide),
    h.scr.ld (d := sU) (n := 8) (by simp only [sU]; omega_arith),
    h.scr.al8 (d := sU) (by simp only [sU]; omega_arith) (by decide),
    h.scr.ld (d := sX) (n := 8) (by simp only [sX]; omega_arith),
    h.scr.al8 (d := sX) (by simp only [sX]; omega_arith) (by decide),
    show sU < 2048 by decide, show sX < 2048 by decide, show sEven < 2048 by decide,
    show sBoth < 2048 by decide, add_ofNat_zero']

/-- Index side conditions of the halvings. -/
macro "twidx" : tactic => `(tactic| ((try simp only [aN, aOne, aT, aU, aX2, wX, wX3, wT2, sU, sX, sEven, sBoth,
  hdr_eq, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and,
  ne_eq]) <;> omega_arith))

/-- `twosFlags`: the low bits of `u` and `x`, `even := ¬u₀` and `both := ¬u₀ ∧ ¬x₀`. -/
theorem twosFlags_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (hN : 63 ≤ N)
    (hN' : N ≤ 2048) :
    WP isa (.block twosFlags) s fun t => Ws t B Z w N ∧ Frame B w [] [sU, sX, sEven, sBoth] s.mem t.mem ∧
      slot t.mem B sEven = (if num s.mem B w aU % 2 = 0 then 1 else 0) ∧
      slot t.mem B sBoth = (if num s.mem B w aU % 2 = 0 ∧ num s.mem B w aX2 % 2 = 0 then 1 else 0) ∧
      Keep opRegs s t := by
  have hsU : sU + 8 ≤ hdr := by decide
  have hsX : sX + 8 ≤ hdr := by decide
  have hsE : sEven + 8 ≤ hdr := by decide
  have hsB : sBoth + 8 ≤ hdr := by decide
  have fX := h.fit64 (j := aX2) (by twidx)
  unfold twosFlags
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (bitOf_ok h (by twidx) hN' hsU (by decide)) fun t1 ⟨h1, k1, o1, r1⟩ => ?_
  refine WP.mono (bitOf_ok h1 (by twidx) hN' hsX (by decide)) fun t2 ⟨h2, k2, o2, r2⟩ => ?_
  rw [k1.num (by simp) (by decide) fX] at o2
  have o1' : slot t2.mem B sU = num s.mem B w aU % 2 := by rw [k2.slot hsU (by decide), o1]
  refine WP.mono (flagsTail_ok h2) fun t ⟨mt, kt⟩ => ?_
  have nw := h2.nowrap
  have hz := h2.hdr_le
  simp only [hdr_eq] at hz
  have sw1 := slot_write (m := t2.mem) (B := B) (w := w) (d := sEven) (word t2.mem B sU ^^^ 1#64)
    (by simp only [sEven]; omega_arith)
  have sw2 := slot_write (m := t2.mem.writeW (off B sEven) (word t2.mem B sU ^^^ 1#64)) (B := B) (w := w)
    (d := sBoth) ((word t2.mem B sX ^^^ 1#64) &&& (word t2.mem B sU ^^^ 1#64)) (by simp only [sBoth]; omega_arith)
  rw [← mt] at sw2
  have bU : (word t2.mem B sU).toNat ≤ 1 := by change slot t2.mem B sU ≤ 1; rw [o1']; omega_arith
  have bX : (word t2.mem B sX).toNat ≤ 1 := by change slot t2.mem B sX ≤ 1; rw [o2]; omega_arith
  have xU : (word t2.mem B sU ^^^ 1#64).toNat = (num s.mem B w aU % 2 + 1) % 2 := by
    rw [xor_bits bU (by decide)]; change (slot t2.mem B sU + 1) % 2 = _; rw [o1']
  have xX : (word t2.mem B sX ^^^ 1#64).toNat = (num s.mem B w aX2 % 2 + 1) % 2 := by
    rw [xor_bits bX (by decide)]; change (slot t2.mem B sX + 1) % 2 = _; rw [o2]
  refine ⟨h2.of_keep kt, (k1.join k2 (js := []) (ds := [sU, sX, sEven, sBoth])).join
    (sw1.1.join sw2.1 (js := []) (ds := [sU, sX, sEven, sBoth])) (js := []) (ds := [sU, sX, sEven, sBoth]), ?_, ?_,
    Keep.trans' r1 (Keep.trans' r2 (Keep.mono kt (by decide)))⟩
  · rw [sw2.1.slot hsE (by decide), sw1.2, xU]
    rcases Nat.mod_two_eq_zero_or_one (num s.mem B w aU) with e | e <;> simp [e]
  · rw [sw2.2, and01 (by rw [xX]; omega_arith) (by rw [xU]; omega_arith), xX, xU]
    rcases Nat.mod_two_eq_zero_or_one (num s.mem B w aU) with e | e <;>
      rcases Nat.mod_two_eq_zero_or_one (num s.mem B w aX2) with f | f <;> simp [e, f]

/-- The masked halving over `n` words at `t0` (`countLoop .t3 halfIfBody`), the mask of `b` in
`a4`: `halfLoop_ok`'s words if `b`, else the same words. -/
theorem halfIfLoop_ok {s : State} {B : Addr} {Z dO n : Nat} (hs : Scr s B Z) {b : Bool}
    (h0 : s.gpr .t0 = off B dO) (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (ha : s.gpr .a4 = if b then BitVec.allOnes 64 else 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO8 : dO % 8 = 0) (hO : dO + 8 * (n + 1) ≤ Z) :
    WP isa (countLoop .t3 halfIfBody) s fun t =>
      (if b then 2 * wordsVal t.mem B dO n + (word s.mem B dO).toNat % 2 =
          wordsVal s.mem B dO n + 2 ^ (64 * n) * ((word s.mem B (dO + 8 * n)).toNat % 2)
        else wordsVal t.mem B dO n = wordsVal s.mem B dO n) ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ Outside B dO (8 * i) s.mem t.mem ∧
      (if b then 2 * wordsVal t.mem B dO i + (word s.mem B dO).toNat % 2 =
          wordsVal s.mem B dO i + 2 ^ (64 * i) * ((word s.mem B (dO + 8 * i)).toNat % 2)
        else wordsVal t.mem B dO i = wordsVal s.mem B dO i) ∧
      Keep [.t0, .t1, .t3, .t5, .t6] s t
  refine WP.mono (wp_countdown (body := .block (halfIfBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, Outside.refl _ _ _ _, by cases b <;> simp [wordsVal], Keep.refl _ _⟩ h3)
    fun t ⟨_, jout, jeq, jk⟩ => ⟨jeq, jout, jk.mono (by decide)⟩
  have hs' := hs.congr jk.2.2
  have ja : t.gpr .a4 = if b then BitVec.allOnes 64 else 0 := (jk.gpr (r := .a4) (by decide)).trans ha
  have hst : WP isa (.block (halfIfBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (word t.mem B (dO + 8 * i) ^^^ (((word t.mem B (dO + 8 * i) >>> 1 |||
            word t.mem B (dO + 8 * i + 8) <<< 63) ^^^ word t.mem B (dO + 8 * i)) &&&
              (if b then BitVec.allOnes 64 else 0)))) ∧
      Keep [.t0, .t1, .t3, .t5, .t6] t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [halfIfBody, j0, ja, hs'.ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.ld (show dO + 8 * i + 8 + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l0, l3, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have wb : word t.mem B (dO + 8 * i + 8) = word s.mem B (dO + 8 * i + 8) :=
      jout.word (by omega_arith) (by omega_arith)
    rw [lm, xsel64, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wa, wb, wordsVal_succ_top s.mem B dO i,
      show dO + 8 * (i + 1) = dO + 8 * i + 8 by omega_arith]
    cases b
    · simp only [Bool.false_eq_true, ite_false] at jeq ⊢
      rw [jeq]
    · simp only [ite_true] at jeq ⊢
      have k := half64_arith (word s.mem B (dO + 8 * i)) (word s.mem B (dO + 8 * i + 8))
      rw [Nat.mul_succ, Nat.pow_add]
      have e : 2 * (2 ^ (64 * i) * (word s.mem B (dO + 8 * i) >>> 1 ||| word s.mem B (dO + 8 * i + 8) <<< 63).toNat) +
          2 ^ (64 * i) * ((word s.mem B (dO + 8 * i)).toNat % 2) =
          2 ^ (64 * i) * (word s.mem B (dO + 8 * i)).toNat +
            2 ^ (64 * i) * 2 ^ 64 * ((word s.mem B (dO + 8 * i + 8)).toNat % 2) := by
        rw [Nat.mul_left_comm, ← Nat.mul_add, k, Nat.mul_add, Nat.mul_assoc]
      grind

/-- `halfIf j sl`: `[j]` halved if the slot `sl` holds 1, in one pass after word `w` := 0. -/
theorem halfIf_ok {s : State} {B : Addr} {Z w N j sl : Nat} (h : Ws s B Z w N) (hN : 63 ≤ N)
    (hN' : N ≤ 2048) (hj : j < N) (_hjT : j ≠ aT) (hsl : sl + 8 ≤ hdr) (hsl8 : sl % 8 = 0)
    (bit : slot s.mem B sl ≤ 1) :
    WP isa (halfIf j sl) s fun t => Ws t B Z w N ∧ Frame B w [aT, j] [] s.mem t.mem ∧
      num t.mem B w j = (if slot s.mem B sl = 0 then num s.mem B w j else num s.mem B w j / 2) ∧
      Keep opRegs s t := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  have hz := h.hdr_le
  rw [halfIf]
  refine WP.seq ?_
  refine ptr_ok h (by decide) (by decide) (show j < 2048 by omega_arith) ?_
  have hb : WP isa (.block [.load .d .a4 .s11 sl, .li .t4 0, .sub .a4 .t4 .a4, .shift .sll .d .t5 .s9 3,
      .add .t5 .t0 .t5, .store .d .t4 .t5 0, mov .t3 .s9]) (s.write .t0 (off B (arr w j))) fun u =>
        (u.gpr .t0 = off B (arr w j) ∧ u.gpr .t3 = BitVec.ofNat 64 w ∧
          u.gpr .a4 = BitVec.ofNat 64 0 - word s.mem B sl ∧
          u.mem = s.mem.writeW (off B (arr w j + 8 * w)) (0 : BitVec 64)) ∧
        Keep [.t3, .t4, .t5, .a4] (s.write .t0 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, fin64_exec_li_zero, h.s9, h.s11, add_ofNat_zero', shl3_ofNat, off_add,
      h.scr.st (d := arr w j + 8 * w) (n := 8) (by omega_arith),
      h.scr.al8 (d := arr w j + 8 * w) (by omega_arith) (by have := arr_al w j; omega_arith),
      h.scr.ld (d := sl) (n := 8) (by have := h.hdr_le; omega_arith),
      h.scr.al8 (d := sl) (by have := h.hdr_le; omega_arith) hsl8,
      show sl < 2048 by have := hdr_eq; omega_arith]
    rfl
  refine WP.mono hb fun u ⟨⟨u0, u3, u4, mu⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  rw [mask_of_slot _ bit] at u4
  refine WP.mono (halfIfLoop_ok hu.scr u0 u3 u4 (by omega_arith) (by omega_arith) (arr_al _ _) (by omega_arith))
    fun t ⟨teq, tout, kt⟩ => ?_
  have ow := writeW_outside s.mem B (d := arr w j + 8 * w) (0 : BitVec 64) (by omega_arith)
  rw [← mu] at ow
  have nu : num u.mem B w j = num s.mem B w j := ow.wordsVal (by omega_arith) (by omega_arith)
  have wz : word u.mem B (arr w j + 8 * w) = 0 := by rw [mu, word_writeW_self]
  refine ⟨hu.of_keep kt, ?_, ?_, Keep.trans' k₁ kt⟩
  · have f1 : Frame B w [aT, j] [] s.mem u.mem := by
      rw [mu]; exact Frame.of_arr (o := j) (d := 8 * w) (n := 8) (writeW_outside _ _ _ (by omega_arith))
        (by omega_arith) (by simp)
    exact f1.trans (Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using tout) (by omega_arith) (by simp))
  · change wordsVal t.mem B (arr w j) w = _
    rw [wz] at teq
    change _ = if (word s.mem B sl).toNat = 0 then wordsVal s.mem B (arr w j) w else wordsVal s.mem B (arr w j) w / 2
    change _ = if _ then num s.mem B w j else num s.mem B w j / 2
    rw [← nu]
    by_cases z : (word s.mem B sl).toNat = 0
    · simp only [z, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false, ite_true] at teq ⊢
      exact teq
    · simp only [z, ne_eq, not_false_eq_true, decide_true, ite_true, ite_false] at teq ⊢
      change 2 * wordsVal t.mem B (arr w j) w + _ = num u.mem B w j + _ at teq
      have m2 := wordsVal_mod2 u.mem B (d := arr w j) (k := w) (by omega_arith)
      change num u.mem B w j % 2 = _ at m2
      have z0 : (0 : BitVec 64).toNat % 2 = 0 := rfl
      rw [z0, Nat.mul_zero, Nat.add_zero] at teq
      change 2 * wordsVal t.mem B (arr w j) w + _ = wordsVal u.mem B (arr w j) w at teq
      change wordsVal u.mem B (arr w j) w % 2 = _ at m2
      show wordsVal t.mem B (arr w j) w = wordsVal u.mem B (arr w j) w / 2
      omega

/-- The masked doubling over `n` words at `t0` (`countLoop .t3 dblIfBody`), the mask of `b` in
`a4`: `shlLoop_ok`'s words if `b`, else the same words; the bit out in `t4` either way. -/
theorem dblIfLoop_ok {s : State} {B : Addr} {Z dO n : Nat} (hs : Scr s B Z) {b : Bool}
    (h0 : s.gpr .t0 = off B dO) (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (h4 : (s.gpr .t4).toNat ≤ 1)
    (ha : s.gpr .a4 = if b then BitVec.allOnes 64 else 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO8 : dO % 8 = 0) (hO : dO + 8 * n ≤ Z) :
    WP isa (countLoop .t3 dblIfBody) s fun t =>
      (t.gpr .t4).toNat ≤ 1 ∧
      (if b then wordsVal t.mem B dO n + 2 ^ (64 * n) * (t.gpr .t4).toNat =
          2 * wordsVal s.mem B dO n + (s.gpr .t4).toNat
        else wordsVal t.mem B dO n = wordsVal s.mem B dO n) ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ (t.gpr .t4).toNat ≤ 1 ∧ Outside B dO (8 * i) s.mem t.mem ∧
      (if b then wordsVal t.mem B dO i + 2 ^ (64 * i) * (t.gpr .t4).toNat =
          2 * wordsVal s.mem B dO i + (s.gpr .t4).toNat
        else wordsVal t.mem B dO i = wordsVal s.mem B dO i) ∧
      Keep [.t0, .t3, .t4, .t5, .t6] s t
  refine WP.mono (wp_countdown (body := .block (dblIfBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j4, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, h4, Outside.refl _ _ _ _, by cases b <;> simp [wordsVal], Keep.refl _ _⟩ h3)
    fun t ⟨_, j4, jout, jeq, jk⟩ => ⟨j4, jeq, jout, jk.mono (by decide)⟩
  have hs' := hs.congr jk.2.2
  have ja : t.gpr .a4 = if b then BitVec.allOnes 64 else 0 := (jk.gpr (r := .a4) (by decide)).trans ha
  have hst : WP isa (.block (dblIfBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (word t.mem B (dO + 8 * i) ^^^ (((word t.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t4) ^^^
            word t.mem B (dO + 8 * i)) &&& (if b then BitVec.allOnes 64 else 0))) ∧
        t'.gpr .t4 = word t.mem B (dO + 8 * i) >>> 63) ∧
      Keep [.t0, .t3, .t4, .t5, .t6] t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [dblIfBody, j0, ja, hs'.ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l0, l3, lm, l4⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l4]; exact (shl64_arith _ _ j4).2
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    rw [lm, xsel64, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wa, wordsVal_succ_top s.mem B dO i]
    cases b
    · simp only [Bool.false_eq_true, ite_false] at jeq ⊢
      rw [jeq]
    · simp only [ite_true] at jeq ⊢
      have k := (shl64_arith (word s.mem B (dO + 8 * i)) (t.gpr .t4) j4).1
      rw [l4, wa, Nat.mul_succ, Nat.pow_add]
      have e : 2 ^ (64 * i) * (word s.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t4).toNat +
          2 ^ (64 * i) * 2 ^ 64 * (word s.mem B (dO + 8 * i) >>> 63).toNat =
          2 * (2 ^ (64 * i) * (word s.mem B (dO + 8 * i)).toNat) + 2 ^ (64 * i) * (t.gpr .t4).toNat := by
        rw [Nat.mul_assoc, ← Nat.mul_add, k, Nat.mul_add, Nat.mul_left_comm]
      grind

/-- `dblIf j sl`: `[j]` doubled modulo `2^(64 w)` if the slot `sl` holds 1, in one pass. -/
theorem dblIf_ok {s : State} {B : Addr} {Z w N j sl : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN' : N ≤ 2048) (hsl : sl + 8 ≤ hdr) (hsl8 : sl % 8 = 0) (bit : slot s.mem B sl ≤ 1) :
    WP isa (dblIf j sl) s fun t => Ws t B Z w N ∧ Frame B w [j] [] s.mem t.mem ∧
      num t.mem B w j = (if slot s.mem B sl = 0 then num s.mem B w j else 2 * num s.mem B w j % 2 ^ (64 * w)) ∧
      Keep opRegs s t := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  rw [dblIf]
  refine WP.seq ?_
  refine ptr_ok h (by decide) (by decide) (show j < 2048 by omega_arith) ?_
  have hb : WP isa (.block [.load .d .a4 .s11 sl, .li .t4 0, .sub .a4 .t4 .a4, mov .t3 .s9])
      (s.write .t0 (off B (arr w j))) fun u =>
        (u.gpr .t0 = off B (arr w j) ∧ u.gpr .t3 = BitVec.ofNat 64 w ∧ u.gpr .t4 = 0 ∧
          u.gpr .a4 = BitVec.ofNat 64 0 - word s.mem B sl ∧ u.mem = s.mem) ∧
        Keep [.t3, .t4, .a4] (s.write .t0 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, fin64_exec_li_zero, h.s9, h.s11, add_ofNat_zero',
      h.scr.ld (d := sl) (n := 8) (by have := h.hdr_le; omega_arith),
      h.scr.al8 (d := sl) (by have := h.hdr_le; omega_arith) hsl8,
      show sl < 2048 by have := hdr_eq; omega_arith]
    rfl
  refine WP.mono hb fun u ⟨⟨u0, u3, u4, ua, mu⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  rw [mask_of_slot _ bit] at ua
  refine WP.mono (dblIfLoop_ok hu.scr u0 u3 (by rw [u4]; decide) ua (by omega_arith) (by omega_arith)
    (arr_al _ _) (by omega_arith)) fun t ⟨_, teq, tout, kt⟩ => ?_
  refine ⟨hu.of_keep kt, ?_, ?_, Keep.trans' k₁ kt⟩
  · rw [← mu]; exact Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using tout) (by omega_arith) (by simp)
  · change wordsVal t.mem B (arr w j) w = _
    rw [mu, u4] at teq
    change _ = if (word s.mem B sl).toNat = 0 then num s.mem B w j else 2 * num s.mem B w j % 2 ^ (64 * w)
    by_cases z : (word s.mem B sl).toNat = 0
    · simp only [z, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false, ite_true] at teq ⊢
      exact teq
    · simp only [z, ne_eq, not_false_eq_true, decide_true, ite_true, ite_false] at teq ⊢
      have z0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [z0, Nat.add_zero] at teq
      rw [← teq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wordsVal_lt _ _ _ _)]

/-- The registers the halvings and the GCD change. -/
abbrev rdRegs : List Reg := .s7 :: .s9 :: .s10 :: opRegs

/-- The halvings' state: `(u, x, 2^k x)`, narrow, narrow, wide. -/
def twosSt (m : Mem) (B : Addr) (w : Nat) : Nat × Nat × Nat :=
  (num m B w aU, num m B w aX2, num m B (W2 w) wX3)

theorem Frame.toNarrow1 {B : Addr} {w j : Nat} {ds : List Nat} {m m' : Mem}
    (h : Frame B (W2 w) [j] ds m m') : Frame B w [2 * j, 2 * j + 1] ds m m' := by
  simpa only [halves, List.flatMap_cons, List.flatMap_nil, List.append_nil] using h.toNarrow

/-- `twosBody`, narrow view to narrow view: one `twoStep` with `b = 64 W`. -/
theorem twosBody_ok {s : State} {B : Addr} {Z w N M : Nat} (h : Ws s B Z w N)
    (hN : 63 ≤ N) (hN' : N ≤ 2048) (hM : 20 ≤ M) (hMN : 2 * M ≤ N) (hW : W2 w ≤ 1024) :
    WP isa twosBody s fun t => Ws t B Z w N ∧
      Frame B w [aU, aX2, aT, 2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1] [sU, sX, sEven, sBoth]
        s.mem t.mem ∧
      twosSt t.mem B w = VG.Proof.Rsa.RecoverDet.twoStep (64 * W2 w) (twosSt s.mem B w) ∧
      t.gpr .s7 = s.gpr .s7 - BitVec.ofNat 64 1 ∧ Keep rdRegs s t := by
  have hsE : sEven + 8 ≤ hdr := by decide
  have hsB : sBoth + 8 ≤ hdr := by decide
  have fU := h.fit64 (j := aU) (by twidx)
  have fX := h.fit64 (j := aX2) (by twidx)
  have hM' : M ≤ 2048 := by omega_arith
  generalize hu : num s.mem B w aU = u
  generalize hx : num s.mem B w aX2 = x
  generalize hX : num s.mem B (W2 w) wX3 = X
  unfold twosBody
  -- 1: the flags.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (twosFlags_ok h hN hN') fun t1 ⟨h1, k1, f1, g1, r1⟩ => ?_
  try simp only [hu, hx] at f1 g1
  -- 2: `u`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (halfIf_ok h1 hN hN' (by twidx) (by twidx) hsE (by decide) (by rw [f1]; split <;> omega_arith))
    fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  rw [f1, k1.num (by simp) (by decide) fU, hu] at e2
  have g2 : slot t2.mem B sBoth = (if u % 2 = 0 ∧ x % 2 = 0 then 1 else 0) := by
    rw [k2.slot hsB (by simp), g1]
  -- 3: `x`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (halfIf_ok h2 hN hN' (by twidx) (by twidx) hsB (by decide) (by rw [g2]; split <;> omega_arith))
    fun t3 ⟨h3, k3, e3, r3⟩ => ?_
  rw [g2, k2.num (by simp [aT, aU, aX2]) (by simp) fX, k1.num (by simp) (by decide) fX, hx] at e3
  have g3 : slot t3.mem B sBoth = (if u % 2 = 0 ∧ x % 2 = 0 then 1 else 0) := by
    rw [k3.slot hsB (by simp), g2]
  have u3 : num t3.mem B w aU = (if (if u % 2 = 0 then 1 else 0) = 0 then u else u / 2) := by
    rw [k3.num (by simp [aT, aU, aX2]) (by simp) fU, e2]
  -- 4: the wide view.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxW_ok h3 hW hMN) fun t4 ⟨⟨h4, m4⟩, k4⟩ => ?_
  have fX3 := h4.fit64 (j := wX3) (by twidx)
  have fT2 := h4.fit64 (j := wT2) (by twidx)
  have X4 : num t4.mem B (W2 w) wX3 = X := by
    rw [m4, k3.toWide.num (by decide) (by simp) fX3, k2.toWide.num (by decide) (by simp) fX3,
      k1.toWide.num (by simp) (by decide) fX3, hX]
  -- 5: `2^k x` doubled if both are even.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have g4 : slot t4.mem B sBoth = (if u % 2 = 0 ∧ x % 2 = 0 then 1 else 0) := by rw [m4, g3]
  refine WP.mono (dblIf_ok h4 (j := wX3) (by twidx) hM' hsB (by decide) (by rw [g4]; split <;> omega_arith))
    fun t7 ⟨h7, k7, e7, r7⟩ => ?_
  rw [g4, X4] at e7
  -- 8: the narrow view, a step less.
  show WP isa (.block (ctxw ++ next)) t7 _
  rw [WP.block_append_iff]
  refine WP.mono (ctxw_ok h7 h.wpos h.fits) fun t8 ⟨⟨h8, m8⟩, k8⟩ => ?_
  have hs : WP isa (.block next) t8 fun u =>
      (u.gpr .s7 = t8.gpr .s7 - BitVec.ofNat 64 1 ∧ u.mem = t8.mem) ∧ Keep [.s7] t8 u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [next]
  refine WP.mono hs fun t ⟨⟨u7, m9⟩, k9⟩ => ?_
  have W8 : Frame B w [2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1] [] t4.mem t7.mem :=
    k7.toNarrow1.mono (by decide) (by simp)
  have fU' := h8.fit64 (j := aU) (by twidx)
  have fX' := h8.fit64 (j := aX2) (by twidx)
  refine ⟨h8.of_keep k9, ?_, ?_, ?_, ?_⟩
  · rw [m9, m8]
    have A : Frame B w [aU, aX2, aT, 2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1] [sU, sX, sEven, sBoth]
        s.mem t3.mem :=
      (k1.join k2 (js := [aU, aX2, aT, 2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1])
        (ds := [sU, sX, sEven, sBoth])).join k3
        (js := [aU, aX2, aT, 2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1]) (ds := [sU, sX, sEven, sBoth])
    rw [← m4] at A
    exact A.join W8
  · have eU : num t.mem B w aU = (if (if u % 2 = 0 then 1 else 0) = 0 then u else u / 2) := by
      rw [m9, m8, W8.num (by simp [aU, wT2, wX3]) (by simp) fU', m4, u3]
    have eX : num t.mem B w aX2 = (if (if u % 2 = 0 ∧ x % 2 = 0 then 1 else 0) = 0 then x else x / 2) := by
      rw [m9, m8, W8.num (by simp [aX2, wT2, wX3]) (by simp) fX', m4, e3]
    have eW : num t.mem B (W2 w) wX3 = (if (if u % 2 = 0 ∧ x % 2 = 0 then 1 else 0) = 0 then X
        else 2 * X % 2 ^ (64 * W2 w)) := by
      rw [m9, m8, e7]
    simp only [twosSt, eU, eX, eW, hu, hx, hX, VG.Proof.Rsa.RecoverDet.twoStep]
    rcases Nat.mod_two_eq_zero_or_one u with a | a <;>
      rcases Nat.mod_two_eq_zero_or_one x with b | b <;> simp [a, b]
  · have r7 : t8.gpr .s7 = s.gpr .s7 := by
      rw [k8.gpr (by decide), r7.gpr (by decide), k4.gpr (by decide),
        r3.gpr (by decide), r2.gpr (by decide), r1.gpr (by decide)]
    rw [u7, r7]
  · exact Keep.trans' (Keep.mono r1 (by decide)) (Keep.trans' (Keep.mono r2 (by decide))
      (Keep.trans' (Keep.mono r3 (by decide)) (Keep.trans' (Keep.mono k4 (by decide))
          (Keep.trans' (Keep.mono r7 (by decide)) (Keep.trans' (Keep.mono k8 (by decide))
            (Keep.mono k9 (by decide)))))))

/-- A subtraction with its borrow is `wsub`. -/
theorem sub_eq_wsub {b x a c β : Nat} (e : x + c = a + 2 ^ b * β) (hx : x < 2 ^ b) (ha : a < 2 ^ b)
    (hc : c < 2 ^ b) (hβ : β ≤ 1) : x = VG.Proof.Rsa.RecoverDet.wsub b a c := by
  unfold VG.Proof.Rsa.RecoverDet.wsub
  rcases (show β = 0 ∨ β = 1 by omega_arith) with rfl | rfl
  · rw [show a + 2 ^ b - c = (a - c) + 2 ^ b by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

/-- `twosInit`, from the wide view: `2^k x := x`; `u := n - 1` and `x := x mod 2^(64 w)` (narrow);
`s7 := 64 w`; the narrow view after. -/
theorem twosInit_ok {s : State} {B : Addr} {Z w N M : Nat} (h : Ws s B Z (W2 w) M)
    (hw : 0 < w) (hNZ : arr w N ≤ Z) (hN : 63 ≤ N) (hN' : N ≤ 2048) (hM : 20 ≤ M) (hMN : 2 * M ≤ N)
    (h1 : num s.mem B w aOne = 0) :
    WP isa twosInit s fun t => Ws t B Z w N ∧
      Frame B w [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2] [] s.mem t.mem ∧
      num t.mem B w aOne = 1 ∧
      twosSt t.mem B w = (VG.Proof.Rsa.RecoverDet.wsub (64 * w) (num s.mem B w aN) 1,
        num s.mem B (W2 w) wX % 2 ^ (64 * w), num s.mem B (W2 w) wX) ∧
      t.gpr .s7 = BitVec.ofNat 64 (64 * w) ∧ Keep rdRegs s t := by
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
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h4 (by twidx) (by twidx) hN' (by twidx)) fun t5 ⟨h5, k5, e5, r5, _⟩ => ?_
  rw [k4.num (by simp [aU, wX]) (by simp) fX, k3.num (by simp [aOne, wX]) (by simp) fX, m2,
    K1.num (by simp [wX, wX3]) (by simp) fX, num_low] at e5
  -- 6: the count.
  have hc : WP isa (.block [.shift .sll .d .s7 .s9 6]) t5 fun t =>
      (t.gpr .s7 = BitVec.ofNat 64 (64 * w) ∧ t.mem = t5.mem) ∧ Keep [.s7] t5 t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h5.s9, shlk_ofNat]
  refine WP.mono hc fun t ⟨⟨c6, m6⟩, k6⟩ => ?_
  have fX3 := h1'.fit64 (j := wX3) (by twidx)
  have fA := h5.fit64 (j := aX2) (by twidx)
  refine ⟨h5.of_keep k6, ?_, ?_, ?_, c6, ?_⟩
  · rw [m6]
    have A := K1
    rw [← m2] at A
    exact (A.join k3 (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2]) (ds := [])).join
      (k4.join k5 (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2]) (ds := []))
      (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2]) (ds := [])
  · rw [m6, k5.num (by simp [aOne, aX2]) (by simp) fO, k4.num (by simp [aOne, aU]) (by simp) fO, e3]
  · simp only [twosSt]
    rw [m6, k5.num (by simp [aU, aX2]) (by simp) fU, u4, e5,
      k5.toWide.num (by decide) (by simp) fX3, k4.toWide.num (by decide) (by simp) fX3,
      k3.toWide.num (by decide) (by simp) fX3, m2, e1]
  · exact Keep.trans' (Keep.mono r1 (by decide)) (Keep.trans' (Keep.mono k2 (by decide))
      (Keep.trans' (Keep.mono r3 (by decide)) (Keep.trans' (Keep.mono r4 (by decide))
        (Keep.trans' (Keep.mono r5 (by decide)) (Keep.mono k6 (by decide))))))

/-- Once the public operand is odd, further masked steps are identities. -/
theorem twoStep_odd {b : Nat} {s : Nat × Nat × Nat} (h : s.1 % 2 = 1) :
    VG.Proof.Rsa.RecoverDet.twoStep b s = s := by
  simp only [VG.Proof.Rsa.RecoverDet.twoStep, show ¬s.1 % 2 = 0 by omega, ↓reduceIte]

/-- A nonzero low `k` bits guarantees an odd operand after `k` halvings. -/
theorem twoStep_odd_bound (b : Nat) : ∀ k (s : Nat × Nat × Nat), s.1 % 2 ^ k ≠ 0 →
    ((VG.Proof.Rsa.RecoverDet.twoStep b)^[k] s).1 % 2 = 1
  | 0, s, h => by simp only [Nat.pow_zero, Nat.mod_one] at h; exact (h rfl).elim
  | k + 1, s, h => by
    by_cases he : s.1 % 2 = 0
    · rw [Function.iterate_succ_apply]
      apply twoStep_odd_bound b k
      rw [VG.Proof.Rsa.RecoverDet.twoStep_fst, ite_eq_left he]
      intro hz
      have hd := Nat.mod_add_div s.1 2
      have hp := Nat.mod_add_div (s.1 / 2) (2 ^ k)
      have hv : s.1 % 2 ^ (k + 1) = 0 := by
        rw [Nat.pow_succ]
        have eq : s.1 = (2 ^ k * 2) * (s.1 / 2 / 2 ^ k) := by
          calc s.1 = 2 * (s.1 / 2) := by omega_arith
               _ = 2 * (2 ^ k * (s.1 / 2 / 2 ^ k)) := congrArg (2 * ·) (by omega_arith)
               _ = _ := by ac_rfl
        rw [eq, Nat.mul_mod_right]
      exact h hv
    · have ho : s.1 % 2 = 1 := by omega
      rw [Function.iterate_fixed (twoStep_odd ho)]
      exact ho

/-- The eight-step result equals the full-width result when the low byte
of `u` is nonzero. -/
theorem twos_short_eq {b n : Nat} (s : Nat × Nat × Nat) (hn : 8 ≤ n) (h : s.1 % 256 ≠ 0) :
    (VG.Proof.Rsa.RecoverDet.twoStep b)^[8] s =
      (VG.Proof.Rsa.RecoverDet.twoStep b)^[n] s := by
  have ho := twoStep_odd_bound b 8 s h
  rw [show n = (n - 8) + 8 by omega_arith, Function.iterate_add_apply]
  exact (Function.iterate_fixed (twoStep_odd ho) (n - 8)).symm

/-- Read the public operand's low byte without changing the working space. -/
theorem twosLow_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (hN : 63 ≤ N) :
    WP isa (.block VG.Impl.Rsa.RISCV64.RecoverDet.twosLow) s fun t =>
      (t.gpr .t4 = BitVec.ofNat 64 (num s.mem B w aU % 256) ∧ t.mem = s.mem) ∧
        Keep [.t0, .t4] s t := by
  have fit := h.arr_fit (show aU < N by simp only [aU]; omega_arith)
  have hw := h.wpos
  have hz := h.hdr_le
  have hS : S w = 8 * (w + 2) := rfl
  have ha : (word s.mem B (arr w aU) &&& BitVec.ofNat 64 255) =
      BitVec.ofNat 64 (num s.mem B w aU % 256) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, show 255 % 2 ^ 64 = 255 by decide]
    rw [
      ← wordsVal_mod64 s.mem B (by omega_arith : 1 ≤ w)]
    have low := Nat.and_two_pow_sub_one_eq_mod (num s.mem B w aU % 2 ^ 64) 8
    simp only [Nat.reducePow, Nat.reduceSub] at low
    rw [low, Nat.mod_mod_of_dvd (num s.mem B w aU) (show 256 ∣ 2 ^ 64 by decide)]
    exact (Nat.mod_eq_of_lt (show num s.mem B w aU % 256 < 2 ^ 64 by
      have := Nat.mod_lt (num s.mem B w aU) (by decide : 0 < 256); omega_arith)).symm
  unfold VG.Impl.Rsa.RISCV64.RecoverDet.twosLow
  refine ptr_ok h (by decide) (by decide) (by decide) ?_
  have hb : WP isa (.block [.load .d .t4 .t0 0, .logicImm .and .t4 .t4 255])
      (s.write .t0 (off B (arr w aU))) fun t =>
      (t.gpr .t4 = BitVec.ofNat 64 (num s.mem B w aU % 256) ∧ t.mem = s.mem) ∧
        Keep [.t4] (s.write .t0 (off B (arr w aU))) t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h.scr.ld (d := arr w aU) (n := 8) (by omega_arith),
      h.scr.al8 (d := arr w aU) (by omega_arith) (arr_al _ _)]
    exact ha
  exact WP.mono hb fun t ⟨ht, kt⟩ => ⟨ht, ((Keep.write _ _ _).trans kt).mono (by decide)⟩

/-- Select the short bound only from the public operand's low byte. -/
theorem twosCount_ok {s : State} {w u : Nat} (hc : s.gpr .s7 = BitVec.ofNat 64 (64 * w))
    (hu : s.gpr .t4 = BitVec.ofNat 64 (u % 256)) :
    WP isa VG.Impl.Rsa.RISCV64.RecoverDet.twosCount s fun t =>
      (t.gpr .s7 = BitVec.ofNat 64 (if u % 256 = 0 then 64 * w else 8) ∧ t.mem = s.mem) ∧
        Keep [.s7] s t := by
  unfold VG.Impl.Rsa.RISCV64.RecoverDet.twosCount
  have hz : (s.gpr .t4 == 0) = decide (u % 256 = 0) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq, hu]
    have hl : u % 256 < 2 ^ 64 := by have := Nat.mod_lt u (by decide : 0 < 256); omega_arith
    constructor
    · intro he
      have ht := congrArg BitVec.toNat he
      change (u % 256) % 2 ^ 64 = 0 at ht
      rwa [Nat.mod_eq_of_lt hl] at ht
    · intro he; rw [he]; rfl
  refine WP.ite _ (VG.RISCV64.Steps.eval_zero s .t4) (fun he => ?_) (fun he => ?_)
  · have he' : u % 256 = 0 := of_decide_eq_true (hz ▸ he)
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [he', hc]
  · have he' : u % 256 ≠ 0 := of_decide_eq_false (hz ▸ he)
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [he', exec_li (imm := 8) (by decide)]

/-- The halvings' state after `i` steps from `s0`. -/
structure TwosI (s0 : State) (B : Addr) (Z w N : Nat) (i : Nat) (t : State) : Prop where
  ws : Ws t B Z w N
  keep : Frame B w [aU, aX2, aT, 2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1] [sU, sX, sEven, sBoth]
    s0.mem t.mem
  regs : Keep rdRegs s0 t
  value : twosSt t.mem B w = (VG.Proof.Rsa.RecoverDet.twoStep (64 * W2 w))^[i] (twosSt s0.mem B w)

/-- `twos`, from the wide view after `d e - 1`: `64 w` steps from `(n - 1, x mod 2^(64 w), x)`,
`n` narrow in `aN` and `x` wide in `wX`; the narrow view after. -/
theorem twos_ok {s : State} {B : Addr} {Z w N M : Nat} (h : Ws s B Z (W2 w) M)
    (hw : 0 < w) (hNZ : arr w N ≤ Z) (hN : 63 ≤ N) (hN' : N ≤ 2048) (hM : 20 ≤ M)
    (hMN : 2 * M ≤ N) (hW : W2 w ≤ 1024) (h1 : num s.mem B w aOne = 0) :
    WP isa twos s fun t => Ws t B Z w N ∧
      Frame B w [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2, aT, 2 * wT2, 2 * wT2 + 1] [sU, sX, sEven, sBoth]
        s.mem t.mem ∧
      num t.mem B w aOne = 1 ∧
      twosSt t.mem B w = (VG.Proof.Rsa.RecoverDet.twoStep (64 * W2 w))^[64 * w]
        (VG.Proof.Rsa.RecoverDet.wsub (64 * w) (num s.mem B w aN) 1,
          num s.mem B (W2 w) wX % 2 ^ (64 * w), num s.mem B (W2 w) wX) ∧
      Keep rdRegs s t := by
  unfold twos
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (twosInit_ok h hw hNZ hN hN' hM hMN h1) fun t0 ⟨h0, k0, o0, e0, c0, r0⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (twosLow_ok h0 hN) fun t1 ⟨⟨l1, m1⟩, r1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (twosCount_ok (w := w) (by rw [r1.gpr (by decide)]; exact c0) l1) fun t2 ⟨⟨c2, m2⟩, r2⟩ => ?_
  let steps := if num t0.mem B w aU % 256 = 0 then 64 * w else 8
  have hsteps : 1 ≤ steps ∧ steps ≤ 64 * w := by unfold steps; split <;> omega_arith
  have hK : steps < 2 ^ 64 := by have := h0.wle; omega_arith
  have h2 := (h0.of_keep r1).of_keep r2
  have r02 : Keep rdRegs t0 t2 := (r1.trans r2).mono (by decide)
  have m02 : t2.mem = t0.mem := m2.trans m1
  change WP isa VG.Impl.Rsa.RISCV64.RecoverDet.twosLoop t2 _
  unfold VG.Impl.Rsa.RISCV64.RecoverDet.twosLoop
  refine WP.mono (wp_countdown (body := twosBody) (cnt := .s7) (N := steps) hK hsteps.1
    (TwosI t0 B Z w N)
    (fun i _ t inv _ => WP.mono (twosBody_ok inv.ws hN hN' hM hMN hW) fun u ⟨hu, ku, eu, cu, ru⟩ =>
      ⟨⟨hu, inv.keep.trans ku, Keep.trans' inv.regs ru, by
        rw [eu, inv.value, Function.iterate_succ_apply']⟩, cu⟩)
    ⟨h2, by rw [m02]; exact Frame.refl _ _ _ _ _, r02, by rw [m02]; rfl⟩ c2) fun t inv => ?_
  have fO := h0.fit64 (j := aOne) (by twidx)
  refine ⟨inv.ws, ?_, ?_, ?_, Keep.trans' r0 inv.regs⟩
  · exact k0.join inv.keep (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2, aT, 2 * wT2, 2 * wT2 + 1])
      (ds := [sU, sX, sEven, sBoth])
  · rw [inv.keep.num (by simp [aOne, aU, aX2, aT, wT2, wX3]) (by decide) fO, o0]
  · rw [inv.value]
    have he : (VG.Proof.Rsa.RecoverDet.twoStep (64 * W2 w))^[steps] (twosSt t0.mem B w) =
        (VG.Proof.Rsa.RecoverDet.twoStep (64 * W2 w))^[64 * w] (twosSt t0.mem B w) := by
      unfold steps
      split
      · rfl
      · rename_i hn; exact twos_short_eq _ (by omega_arith) hn
    rw [he, e0]

end VG.Proof.Rsa.RISCV64.Keys
