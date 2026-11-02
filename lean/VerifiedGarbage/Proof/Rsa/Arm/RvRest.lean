module

public import VerifiedGarbage.Proof.Rsa.Arm.RvFin5
public import VerifiedGarbage.Proof.Rsa.Arm.RvCand5
import VerifiedGarbage.Proof.Rsa.RecoverTries
import VerifiedGarbage.Proof.Rsa.Arm.RvHalving
import VerifiedGarbage.Proof.Rsa.RecoverSubtract

/-! # `vg_rsa_recover_primes` on ARMv7: from `m = 2^t r` to the factors (`rest_vp`)

Once `n` is valid and `d e - 1` is even and positive: the halvings, the
candidates and the factors, with `recoverPrimes`'s result
(`result_eq`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n sqRes)
open VG.Spec.Rsa (recoverPrimes recoverStep recoverTries splitTwos)

section
variable {P : RP}

/-- Shared factor extraction for either recovery search. -/
theorem finWith_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] (hn : P.n % 2 = 1 ∧ 1 < P.n) (nl : P.n < 2 ^ (32 * P.w))
    {E : State → Prop} (F : FinishInputs P) :
    VP (FinishStart P E F) fin (Fe (F := F) P E) := by
  have hn0 : 0 < P.n := by omega
  simp only [fin, seqs]
  exact VP.seq (finYWith_vp hn F) (VP.seq (gcdSet_vp hn nl F)
    (VP.seq (inverse_vp hn nl F) (VP.seq (divSet_vp F)
      (VP.seq (div_vp hn0 F) (VP.seq (order_vp hn0 nl F) (stores_vp hn0 F))))))

theorem fin_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] (hn : P.n % 2 = 1 ∧ 1 < P.n) (nl : P.n < 2 ^ (32 * P.w)) {E : State → Prop} :
    VP (Cf P E (Jl P)) fin (Fe P E) := by
  have hn0 : 0 < P.n := by omega
  simp only [fin, seqs]
  exact VP.seq (finY_vp hn) (VP.seq (gcdSet_vp hn nl) (VP.seq (inverse_vp hn nl) (VP.seq divSet_vp
    (VP.seq (div_vp hn0) (VP.seq (order_vp hn0 nl) (stores_vp hn0))))))

/-- The candidates' `m`. -/
theorem mv_facts {σ : State} (hg : goOn P σ = true) :
    mv P σ = dv P σ * P.e - 1 ∧ ¬(dv P σ * P.e < 2 ∨ (dv P σ * P.e - 1) % 2 = 1) ∧ 0 < mv P σ ∧
      mv P σ % 2 = 0 := by
  simp only [goOn, decide_eq_true_eq] at hg
  simp only [mv, Mv] at *
  omega

theorem M_lt {σ : State} (pre : In P σ) : Mv P σ < 2 ^ P.c := by
  have he : P.e < 2 ^ (8 * P.el) := by have := bytes_lt σ.mem (State.addr P.eP) P.el; rwa [pre.eB] at this
  have hd : dv P σ < 2 ^ (8 * P.dl) := bytes_lt σ.mem (State.addr P.dP) P.dl
  calc dv P σ * P.e < 2 ^ (8 * P.dl) * 2 ^ (8 * P.el) := Nat.mul_lt_mul'' hd he
    _ = 2 ^ P.c := by rw [← Nat.pow_add]; simp only [RP.c]; congr 1; omega

theorem hvs_eq {σ : State} (pre : In P σ) (hg : goOn P σ = true) :
    hvs P σ P.c = ((splitTwos (mv P σ)).2, (splitTwos (mv P σ)).1) := by
  obtain ⟨-, -, h0, -⟩ := mv_facts hg
  have := M_lt pre
  exact VG.Proof.Rsa.halve_done h0 (by simp only [mv] at *; omega)

/-- `primesKey`'s number of tries. -/
theorem primesKey_snd (hv : Spec.Rsa.modulusValid P.n P.K = true) {σ : State} (pre : In P σ) :
    (Spec.Rsa.primesKey P.nB P.eB (dB P σ)).2 = (recoverPrimes P.n P.e (dv P σ)).2 := by
  have hl : P.nB.length = P.K := by rw [← pre.nB]; simp [Spec.Rsa.bytesAt]
  simp only [Spec.Rsa.primesKey, hl, show Spec.Rsa.os2ip P.nB = P.n from rfl, hv, ite_true]
  rcases recoverPrimes P.n P.e (dv P σ) with ⟨_ | ⟨p, q⟩, t⟩ <;> rfl

theorem rest_facts (hv : Spec.Rsa.modulusValid P.n P.K = true) {σ : State} (pre : In P σ)
    (hg : goOn P σ = true) (tr : Tries P σ) :
    1 ≤ tv P σ ∧ tv P σ ≤ P.c ∧ rv P σ < 2 ^ P.c ∧ (gos P σ 100).2 = P.nt := by
  obtain ⟨e1, e2, h0, h2⟩ := mv_facts hg
  have hM := M_lt pre
  have hm : mv P σ < 2 ^ P.c := by simp only [mv] at *; omega
  have ev := hvs_eq pre hg
  have tv_eq : tv P σ = (splitTwos (mv P σ)).1 := by simp only [tv, ev]
  have rv_eq : rv P σ = (splitTwos (mv P σ)).2 := by simp only [rv, ev]
  obtain ⟨s1, s2⟩ := VG.Proof.Rsa.splitTwos_spec h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tv_eq, VG.Proof.Rsa.splitTwos_even (by omega) h2]; omega
  · rw [tv_eq]; exact Nat.le_of_lt (VG.Proof.Rsa.splitTwos_lt h0 hm)
  · rw [rv_eq]
    have : (splitTwos (mv P σ)).2 ≤ mv P σ := by
      conv => rhs; rw [s1]
      exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    omega
  · rw [← tr, primesKey_snd hv pre, VG.Proof.Rsa.recoverPrimes_go e2, ← e1]
    show (recoverPrimes.go P.n (tv P σ) (rv P σ) recoverTries).2 = _
    rw [tv_eq, rv_eq]

/-- `primesKey`'s result. -/
theorem primesKey_fst (hv : Spec.Rsa.modulusValid P.n P.K = true) {σ : State} (pre : In P σ)
    (hg : goOn P σ = true) :
    (Spec.Rsa.primesKey P.nB P.eB (dB P σ)).1 =
      (gos P σ 100).1.map fun v => (Spec.Rsa.i2osp v.1 P.K, Spec.Rsa.i2osp v.2 P.K) := by
  have hl : P.nB.length = P.K := by rw [← pre.nB]; simp [Spec.Rsa.bytesAt]
  obtain ⟨e1, e2, -, -⟩ := mv_facts hg
  have ev := hvs_eq pre hg
  have hr : recoverPrimes P.n P.e (dv P σ) = gos P σ 100 := by
    rw [VG.Proof.Rsa.recoverPrimes_go e2, ← e1]
    show _ = recoverPrimes.go P.n (hvs P σ P.c).2 (hvs P σ P.c).1 recoverTries
    rw [ev]
  simp only [Spec.Rsa.primesKey, hl, show Spec.Rsa.os2ip P.nB = P.n from rfl, hv, ite_true]
  show (match recoverPrimes P.n P.e (dv P σ) with
    | (some (p, q), tries) => (some (Spec.Rsa.i2osp p P.K, Spec.Rsa.i2osp q P.K), tries)
    | (none, tries) => (none, tries)).1 = _
  rw [hr]
  rcases gos P σ 100 with ⟨_ | ⟨p, q⟩, t⟩ <;> rfl

theorem sub32_one {w y : Nat} (h1 : 1 ≤ y) (h2 : y < 2 ^ (32 * w)) : sub32 w y 1 = y - 1 :=
  VG.Proof.Rsa.sub32_one h1 h2

/-- The result: the factors if the last candidate gave them. -/
theorem resultWith_eq (hv : Spec.Rsa.modulusValid P.n P.K = true) (hn1 : 1 < P.n) (nl : P.n < 2 ^ (32 * P.w))
    {σ : State} (pre : In P σ) (hg : goOn P σ = true) (tr : Tries P σ)
    (hgo : gos P σ 100 = gos P σ (100 - Jl P)) (hnt1 : 1 ≤ P.nt) (F : FinishInputs P)
    (rootEq : (if F.ok σ then some (F.value σ) else none) =
      recoverStep P.n (tv P σ) (rv P σ) (Jl P + 2)) :
    (Spec.Rsa.primesKey P.nB P.eB (dB P σ)).1 =
      if okF (F := F) P σ then some (Spec.Rsa.i2osp (bigF (F := F) P σ) P.K, Spec.Rsa.i2osp (smallF (F := F) P σ) P.K) else none := by
  obtain ⟨-, -, -, hnt⟩ := rest_facts hv pre hg tr
  have hle : P.nt ≤ 100 := by rw [← hnt]; exact VG.Proof.Rsa.go_le _ _ _ _ (Nat.le_refl _)
  have hJ : Jl P < recoverTries := by unfold recoverTries; simp only [Jl]; omega
  have g := VG.Proof.Rsa.go_eq P.n (tv P σ) (rv P σ) hJ
  have hgo2 : recoverPrimes.go P.n (tv P σ) (rv P σ) recoverTries =
      recoverPrimes.go P.n (tv P σ) (rv P σ) (recoverTries - Jl P) := hgo
  rw [primesKey_fst hv pre hg]
  show Option.map _ (recoverPrimes.go P.n (tv P σ) (rv P σ) recoverTries).1 = _
  rw [hgo2, g]
  cases hs : recoverStep P.n (tv P σ) (rv P σ) (Jl P + 2) with
  | some y =>
    have link : (if F.ok σ then some (F.value σ) else none) = some y := by
      simpa only [hs] using rootEq
    have hok : okF (F := F) P σ = true := by
      by_contra no
      have no' : F.ok σ = false := Bool.eq_false_iff.mpr no
      simp only [no', Bool.false_eq_true, ite_false] at link
      cases link
    have hy : yF (F := F) P σ = y := by
      change F.ok σ = true at hok
      simpa only [hok, ite_true, Option.some.injEq] using link
    have y1 := VG.Proof.Rsa.recoverStep_some hs
    have hy1 : 1 ≤ y := by
      rcases Nat.eq_zero_or_pos y with h | h
      · rw [h] at y1; simp at y1
      · exact h
    have hyn : y < P.n := by rw [← hy]; exact F.bounded σ (by omega)
    have ym : ym1 (F := F) P σ = y - 1 := by simp only [ym1]; rw [hy]; exact sub32_one hy1 (by omega)
    rw [hok]
    simp only [ite_true, Option.map_some, bigF, smallF, qF, pF, ym]
  | none =>
    have link : (if F.ok σ then some (F.value σ) else none) = none := by
      simpa only [hs] using rootEq
    have hok : okF (F := F) P σ = false := by
      by_cases yes : F.ok σ = true
      · simp only [yes, ite_true] at link; cases link
      · exact Bool.eq_false_iff.mpr yes
    have hnt2 : (recoverPrimes.go P.n (tv P σ) (rv P σ) recoverTries).2 = P.nt := hnt
    have hj : Jl P < (recoverPrimes.go P.n (tv P σ) (rv P σ) recoverTries).2 := by rw [hnt2]; simp only [Jl]; omega
    have cc := VG.Proof.Rsa.cand_cond P.n (tv P σ) (rv P σ) (j := Jl P) hj hgo2
    rw [hs, hnt2] at cc
    have h100 : Jl P + 1 = 100 := by
      simp only [Option.isSome_none, Bool.not_false, Bool.and_true, Bool.not_not] at cc
      have : decide (Jl P + 1 < 100) = false := by rw [cc]; simp only [Jl]; simp; omega
      simp at this; simp only [Jl] at *; omega
    rw [hok]
    show Option.map _ (recoverPrimes.go P.n (tv P σ) (rv P σ) (recoverTries - (Jl P + 1))).1 = none
    rw [show recoverTries - (Jl P + 1) = recoverTries - recoverTries by rw [h100]; rfl, VG.Proof.Rsa.go_last]
    rfl

theorem result_eq (hv : Spec.Rsa.modulusValid P.n P.K = true) (hn1 : 1 < P.n) (nl : P.n < 2 ^ (32 * P.w))
    {σ : State} (pre : In P σ) (hg : goOn P σ = true) (tr : Tries P σ)
    (hgo : gos P σ 100 = gos P σ (100 - Jl P)) (hnt1 : 1 ≤ P.nt) :
    (Spec.Rsa.primesKey P.nB P.eB (dB P σ)).1 =
      if okF P σ then some (Spec.Rsa.i2osp (bigF P σ) P.K, Spec.Rsa.i2osp (smallF P σ) P.K) else none := by
  obtain ⟨ht1, htc, -, -⟩ := rest_facts hv pre hg tr
  refine resultWith_eq hv hn1 nl pre hg tr hgo hnt1 (legacyFinish P) ?_
  change sqRes (sqst P σ (Jl P) P.c) = _
  exact VG.Proof.Rsa.sq_result ht1 htc

/-- Facts of a valid modulus. -/
theorem valid_facts (hv : Spec.Rsa.modulusValid P.n P.K = true) (hk : 2 ≤ P.K) :
    P.n % 2 = 1 ∧ 1 < P.n ∧ 101 < P.n := by
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
  have h1 := hv.1.1.1
  have h2 := hv.2
  have : 256 ^ 1 ≤ 256 ^ (P.K - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have : (256 : Nat) ^ 1 = 256 := rfl
  omega

/-- The stage the candidates start from: `n` valid, and `d e - 1` even and positive. -/
abbrev E1 (P : RP) (σ : State) : Prop := In P σ ∧ goOn P σ = true ∧ Tries P σ

/-- From `m = 2^t r` to the factors. -/
theorem rest_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] (hv : Spec.Rsa.modulusValid P.n P.K = true) :
    VP (fun σ s => E1 P σ ∧ KS P σ (Aload P σ) [aN] (AWs P σ) [wM, wZ] (Vs P σ) [sBit] s ∧ Ws s P.B P.Z P.W 22)
      rest (Fe P (Ej P (E1 P) (Jl P))) := by
  refine VP.of_imp (p := Sizes P ∧ 1 ≤ P.nt ∧ P.nt ≤ 100 ∧ 0 < P.c ∧ P.c < 2 ^ 31 ∧ P.n < 2 ^ (32 * P.w) ∧
    2 ≤ P.K) (fun σ s ⟨⟨pre, hg, tr⟩, _⟩ => ?_) fun ⟨hs, hnt1, hnt2, hc0, hcl, nl, hk⟩ => ?_
  · obtain ⟨-, -, -, hnt⟩ := rest_facts hv pre hg tr
    have := pre.el1; have := pre.dl1; have := pre.el2; have := pre.dl2; have := pre.k2; have := pre.k1
    refine ⟨pre.sizes, ?_, ?_, by simp only [RP.c]; omega, by simp only [RP.c]; omega, n_lt pre, by omega⟩
    · rw [← hnt]; exact VG.Proof.Rsa.go_pos _ _ _ _ (Nat.le_refl _)
    · rw [← hnt]; exact VG.Proof.Rsa.go_le _ _ _ _ (Nat.le_refl _)
  obtain ⟨hn1, hn2, h101⟩ := valid_facts hv hk
  have hn : P.n % 2 = 1 ∧ 1 < P.n := ⟨hn1, hn2⟩
  simp only [rest, seqs]
  exact VP.seq (halving_vp fun _ _ => hc0) (VP.seq (mont_vp hn hs) (VP.seq
    (candLoop_vp hn h101 hcl hc0 hnt1 hnt2 fun σ e => rest_facts hv e.1 e.2.1 e.2.2) (fin_vp hn nl)))

end

end VG.Proof.Rsa.Arm.Recover
