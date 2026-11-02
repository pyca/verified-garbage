module

public import VerifiedGarbage.Proof.Rsa.RISCV64.RdLoad
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.RISCV64.RdTwos
import VerifiedGarbage.Proof.Rsa.RISCV64.RdStage2
import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValInv
import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValFront
import VerifiedGarbage.Proof.Rsa.RecoverDet
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on RISC-V: correctness

The second half of the function, after `d e - 1` (`RdLoad`'s `Dm`), as
`Proof/Rsa/RecoverDetModel.lean` models it: `stA_ok` runs the halvings, the
GCD and the first division (`St3`), `stB_ok` the second division, `b² - 4 n`,
the square root and the factors (`Det`), with the mask the model's
(`mask_eq`) and the code's quotient and remainder where the divisor is
positive. `stores_ok`: the factors written under the mask and the mask
returned; `valid_ok`: a valid modulus, from the set-up to the stores;
`rd_correct`: the function, through `RecoverDet.model_correct`, on the
registers and the stack (`fnPost`).
-/

-- separate module: its proofs (the stages chained, the stores and `rd_correct`) are not re-checked with
-- every change to the constant-time proof

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.RecDet

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Proof.Rsa.RecoverDet (deX okDE wsub wsub_of_le twoStep twosOut aOf ltOf m1Of dOf sqOf fourN xOf
  rootOf stage2 twos_iter prod_iter)
open VG.Impl.Rsa.RISCV64.Keys (seqs)
open VG.Impl.Rsa.RISCV64.RecoverDet (twos gcd divA divB minus4n sqrt factors nArr aN aOne aZero aU aX2 aT
  gU gV gT1 gT2 gT3 aNeg1 aM1 aD aRem aDt aRm aSy aTy aDf aP aQ aNy wZ wE wD wM wMod wT wX wOne wX3 wA wR wN
  wDt wT2 wG wB wSq sB0 sB1 sU sX sEven sBoth sLt sExact sC1 sC2 sBb sOk5 sMask)
open VG.Impl.Rsa.RISCV64.Keys (sOdd sB sC)
open VG.Proof.Rsa.RISCV64.CrtValues (bit_ite bytes_in bytes_sep bytesAt_congr zeros_keep bytesAt_zero
  wordsVal_of_out)

/-- Index side conditions. -/
macro "rdc" : tactic => `(tactic| ((try simp only [nArr, nWide, aN, aOne, aZero, aU, aX2, aT, gU, gV, gT1,
  gT2, gT3, aNeg1, aM1, aD, aRem, aDt, aRm, aSy, aTy, aDf, aP, aQ, aNy, wZ, wE, wD, wM, wMod, wT, wX, wOne,
  wX3, wA, wR, wN, wDt, wT2, wG, wB, wSq, sB0, sB1, sU, sX, sEven, sBoth, sLt, sExact, sC1, sC2, sBb, sOk5,
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
  have un : wsub nb n 1 = n - 1 := wsub_of_le hn (by omega_arith)
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

/-- The product of the checks' slots is the model's mask. -/
theorem mask_eq {nb wb n de q rem B0 B1 Lt Ex C1 C2 Ok : Nat}
    (b0 : B0 = if de < 1 then 1 else 0) (b1 : B1 = if deX wb de < 1 then 1 else 0)
    (lt : Lt = if aOf nb wb n de / n < n then 1 else 0) (ex : Ex = if rem = 0 then 1 else 0)
    (c1 : C1 = if sqOf nb wb (RecoverDet.bOf nb q) < fourN wb n then 1 else 0)
    (c2 : C2 = if xOf nb wb n (RecoverDet.bOf nb q) < 1 then 1 else 0)
    (ok : Ok = if (rootOf nb wb n (RecoverDet.bOf nb q)).2.1 = 0 then 1 else 0) :
    (1 - B0) * (1 - B1) * Lt * Ex * (1 - C1) * (1 - C2) * Ok =
      (okDE wb de && ltOf nb wb n de && (stage2 nb wb n q rem).1).toNat := by
  subst b0 b1 lt ex c1 c2 ok
  simp only [ite_toNat]
  rw [mask_bool]
  rfl

/-! ## The halvings, the GCD and `a`, `m`, `r` -/

/-- The narrow arrays written by each stage. -/
abbrev u1 : List Nat := dmUsed ++ [22, 23, 41, 43, 44, 45]
abbrev u2 : List Nat := u1 ++ [46, 47, 48, 49, 50, 34]
abbrev u3 : List Nat := u2 ++ [28, 29, 24, 25, 26, 27, 30, 31]
abbrev u4 : List Nat := u3 ++ [51, 52, 53, 54, 55]
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
  a : num t.mem (bOf s0) (WOf s0) wA = aOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) / Nv s0
  r : num t.mem (bOf s0) (WOf s0) wR = aOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) % Nv s0
  lt : slot t.mem (bOf s0) sLt = if aOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) / Nv s0 < Nv s0 then 1 else 0
  free : ∀ j < nArr, j ∉ u3 → wordsVal t.mem (bOf s0) (arr (wOf s0) j) (wOf s0 + 2) = 0

theorem stA_ok {s0 s : State} (h : PreC s0) (three : 3 ≤ Nv s0) (dm : Dm s0 s) :
    WP isa (seqs [twos, gcd, divA]) s (St3 s0) := by
  have ⟨b8, _, _, _, nk⟩ := bounds h
  have ⟨f1, f2⟩ := h.fits
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have wpos : 0 < wOf s0 := by simp only [wOf]; omega_arith
  have hk : kOf s0 ≤ 1024 := h.k2
  -- The halvings.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (twos_ok (N := nArr) dm.ws wpos f1 (by decide) (by decide) (by decide) (by decide) f2
    (num_zero (dm.free _ (by rdc) (by rdc)))) fun t1 ⟨w1, F1, one1, st1, k1⟩ => ?_
  have c1 := dm.cb.step w1 F1 (by rdc) (by rdc) k1
  have fr1 := free_step (U' := u1) F1 (by rdc) fit (by rdc) (by rdc) dm.free
  have n1 : num t1.mem (bOf s0) (wOf s0) aN = Nv s0 := by rw [F1.num (by rdc) (by rdc) (fit _ (by rdc)), dm.n]
  have tw : twosSt t1.mem (bOf s0) (wOf s0) = twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) := by
    rw [st1, dm.n, dm.x]; rfl
  obtain ⟨uo, ul, x2l⟩ := twos_out (wb := wbOf s0) (de := deOf s0) three (show Nv s0 < 2 ^ nbOf s0 by omega_arith)
  have u1v : num t1.mem (bOf s0) (wOf s0) aU = (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).1 := by
    rw [← tw]; rfl
  have x21 : num t1.mem (bOf s0) (wOf s0) aX2 = (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).2.1 := by
    rw [← tw]; rfl
  have x31 : num t1.mem (bOf s0) (WOf s0) wX3 = (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).2.2 := by
    rw [← tw]; rfl
  -- The GCD.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (gcd_ok w1 (L := kOf s0) (by decide) (by decide)
    (by rw [c1.s2, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_arith)) fun t2 ⟨w2, F2, hi2, g2, k2⟩ => ?_
  have c2 := c1.step w2 F2 (by rdc) (by rdc) k2
  have fr2 := free_step (U' := u2) F2 (by rdc) fit (by rdc) (by rdc) fr1
  have n2 : num t2.mem (bOf s0) (wOf s0) aN = Nv s0 := by rw [F2.num (by rdc) (by rdc) (fit _ (by rdc)), n1]
  have bnd : num t1.mem (bOf s0) (wOf s0) aX2 * num t1.mem (bOf s0) (wOf s0) aU < 2 ^ (64 * wOf s0 + 8 * kOf s0) := by
    rw [x21, u1v, Nat.pow_add]
    exact Nat.mul_lt_mul'' x2l (by omega_arith)
  have G : num t2.mem (bOf s0) (WOf s0) wG =
      Nat.gcd (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).2.1 (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).1 := by
    rw [numW_low (by rw [hi2]; exact hiW_zero (fr1 _ (by rdc) (by rdc)) (fr1 _ (by rdc) (by rdc))),
      g2 (by rw [u1v]; exact uo) bnd, x21, u1v]
  have X3 : num t2.mem (bOf s0) (WOf s0) wX3 = (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).2.2 := by
    rw [numW_of F2 (by rdc) (by rdc) (fit _ (by rdc)), x31]
  have aof : aOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) =
      num t2.mem (bOf s0) (WOf s0) wG * num t2.mem (bOf s0) (WOf s0) wX3 % 2 ^ (64 * WOf s0) := by
    rw [G, X3]
    refine aOf_eq (by rw [← x31]; exact wordsVal_lt _ _ _ _) ?_
    have := Nat.gcd_le_left (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).2.1
      (show 0 < (twosOut (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)).1 by omega_arith)
    omega_arith
  -- `a`, `m` and `r`.
  refine WP.mono (divA_ok (show Ws t2 (bOf s0) (zOf s0) (wOf s0) 63 from w2) f2
    (hiW_zero (fr2 _ (by rdc) (by rdc)) (fr2 _ (by rdc) (by rdc)))
    (word_zero_of (fr2 _ (by rdc) (by rdc)) (by omega_arith))
    (num_zero (wide_zero (fr2 _ (by rdc) (by rdc)) (fr2 _ (by rdc) (by rdc))))) fun t3 ⟨w3, F3, k3, v3⟩ => ?_
  have c3 := c2.step w2 F3 (by rdc) (by rdc) k3
  have fr3 := free_step (U' := u3) F3 (by rdc) fit (by rdc) (by rdc) fr2
  obtain ⟨vN, vA, vR, vLt⟩ := v3 (by rw [n2]; omega_arith)
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
  div : 0 < m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) →
    q = dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) / m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) ∧
    rem = dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) % m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)
  mask : slot t.mem (bOf s0) sMask = (okDE (wbOf s0) (deOf s0) && ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) &&
    (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).1).toNat
  p : num t.mem (bOf s0) (wOf s0) aP = (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).2.1
  q : num t.mem (bOf s0) (wOf s0) aQ = (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).2.2

theorem stB_ok {s0 s : State} (h : PreC s0) (st : St3 s0 s) :
    WP isa (seqs [divB, minus4n, sqrt, factors]) s fun t => ∃ q rem, Det s0 q rem t := by
  have ⟨_, _, hw2, _, _⟩ := bounds h
  have ⟨f1, f2⟩ := h.fits
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have wpos : 0 < wOf s0 := by simp only [wOf]; omega_arith
  -- `m + 1`, `n - r`, their quotient and remainder.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (divB_ok st.ws f1 wpos (num_zero (st.free _ (by rdc) (by rdc))) st.one
    (word_zero_of (st.free _ (by rdc) (by rdc)) (by omega_arith))) fun t4 ⟨w4, F4, k4, neg4, m14, dv4, ex4⟩ => ?_
  have c4 := st.cb.step w4 F4 (by rdc) (by rdc) k4
  have fr4 := free_step (U' := u4) F4 (by rdc) fit (by rdc) (by rdc) st.free
  have vm1 : num t4.mem (bOf s0) (wOf s0) aM1 = m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) := by
    rw [m14, st.a]; rfl
  have hdiv : 0 < m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) →
      num t4.mem (bOf s0) (wOf s0) aD =
        dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) / m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) ∧
      num t4.mem (bOf s0) (wOf s0) aRem =
        dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) % m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) := by
    intro hp
    obtain ⟨d1, d2⟩ := dv4 (by rw [vm1]; exact hp)
    rw [vm1, st.n, st.r] at d1 d2
    exact ⟨d1, d2⟩
  -- `b`, `b²`, `4 n` and `b² - 4 n`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (minus4n_ok w4 f2 neg4 (hiW_zero (fr4 _ (by rdc) (by rdc)) (fr4 _ (by rdc) (by rdc)))
    (num_zero (wide_zero (fr4 _ (by rdc) (by rdc)) (fr4 _ (by rdc) (by rdc))))
    (by rw [numW_of F4 (by rdc) (by rdc) (fit _ (by rdc)), st.oneW]))
    fun t5 ⟨w5, F5, k5, d5, sq5, n5, r5, c15, c25⟩ => ?_
  have c5 := c4.step w4 F5 (by rdc) (by rdc) k5
  have fr5 := free_step (U' := u5) F5 (by rdc) fit (by rdc) (by rdc) fr4
  have b5 : num t5.mem (bOf s0) (wOf s0) aD =
      RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD) := d5
  have bl : RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD) < 2 ^ nbOf s0 :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have sqv : num t5.mem (bOf s0) (WOf s0) wSq =
      sqOf (nbOf s0) (wbOf s0) (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD)) := by
    rw [sq5, b5, sqOf_eq bl (by omega_arith)]
  have nWv : num t4.mem (bOf s0) (WOf s0) wN = Nv s0 := by
    rw [numW_of F4 (by rdc) (by rdc) (fit _ (by rdc)), st.nW]
  have fN : num t5.mem (bOf s0) (WOf s0) wN = fourN (wbOf s0) (Nv s0) := by rw [n5, nWv]
  have xv : num t5.mem (bOf s0) (WOf s0) wR =
      xOf (nbOf s0) (wbOf s0) (Nv s0) (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD)) := by
    rw [r5, sqv, fN]; rfl
  -- The square root.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sqrt_ok w5 f1 wpos f2 (num_zero (fr5 _ (by rdc) (by rdc))) (num_zero (fr5 _ (by rdc) (by rdc)))
    (num_zero (fr5 _ (by rdc) (by rdc)))) fun t6 ⟨w6, F6, k6, rm6, sy6, ok6⟩ => ?_
  have c6 := c5.step w4 F6 (by rdc) (by rdc) k6
  have fr6 := free_step (U' := u6) F6 (by rdc) fit (by rdc) (by rdc) fr5
  have rmv : num t6.mem (bOf s0) (wOf s0) aRm =
      (rootOf (nbOf s0) (wbOf s0) (Nv s0) (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD))).2.1 := by
    rw [rm6, xv]; rfl
  have syv : num t6.mem (bOf s0) (wOf s0) aSy =
      (rootOf (nbOf s0) (wbOf s0) (Nv s0) (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD))).2.2 := by
    rw [sy6, xv]; rfl
  have d6 : num t6.mem (bOf s0) (wOf s0) aD = RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD) := by
    rw [F6.num (by rdc) (by rdc) (fit _ (by rdc)), b5]
  -- The checks' slots.
  have b0 : slot t6.mem (bOf s0) sB0 = if deOf s0 < 1 then 1 else 0 := by
    rw [F6.slot (by rdc) (by rdc), F5.slot (by rdc) (by rdc), F4.slot (by rdc) (by rdc), st.b0]
  have b1 : slot t6.mem (bOf s0) sB1 = if deX (wbOf s0) (deOf s0) < 1 then 1 else 0 := by
    rw [F6.slot (by rdc) (by rdc), F5.slot (by rdc) (by rdc), F4.slot (by rdc) (by rdc), st.b1]
  have lt : slot t6.mem (bOf s0) sLt =
      if aOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) / Nv s0 < Nv s0 then 1 else 0 := by
    rw [F6.slot (by rdc) (by rdc), F5.slot (by rdc) (by rdc), F4.slot (by rdc) (by rdc), st.lt]
  have ex : slot t6.mem (bOf s0) sExact = if num t4.mem (bOf s0) (wOf s0) aRem = 0 then 1 else 0 := by
    rw [F6.slot (by rdc) (by rdc), F5.slot (by rdc) (by rdc), ex4]
  have c1 : slot t6.mem (bOf s0) sC1 = if sqOf (nbOf s0) (wbOf s0)
      (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD)) < fourN (wbOf s0) (Nv s0) then 1 else 0 := by
    rw [F6.slot (by rdc) (by rdc), c15, sqv, fN]
  have c2 : slot t6.mem (bOf s0) sC2 = if xOf (nbOf s0) (wbOf s0) (Nv s0)
      (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD)) < 1 then 1 else 0 := by
    rw [F6.slot (by rdc) (by rdc), c25, xv]
  have ok : slot t6.mem (bOf s0) sOk5 = if (rootOf (nbOf s0) (wbOf s0) (Nv s0)
      (RecoverDet.bOf (nbOf s0) (num t4.mem (bOf s0) (wOf s0) aD))).2.1 = 0 then 1 else 0 := by
    rw [ok6, rmv]
  -- The factors.
  refine WP.mono (factors_ok w6 (num_zero (fr6 _ (by rdc) (by rdc))) (by rw [b0]; exact bit_ite)
    (by rw [b1]; exact bit_ite) (by rw [lt]; exact bit_ite) (by rw [ex]; exact bit_ite)
    (by rw [c1]; exact bit_ite) (by rw [c2]; exact bit_ite) (by rw [ok]; exact bit_ite))
    fun t7 ⟨w7, F7, k7, p7, q7, mk7⟩ => ?_
  have c7 := c6.step w6 F7 (by rdc) (by rdc) k7
  exact ⟨_, _, c7, w7, hdiv, by rw [mk7]; exact mask_eq b0 b1 lt ex c1 c2 ok, by rw [p7, d6, syv]; rfl,
    by rw [q7, d6, syv]; rfl⟩

/-! ## The stores -/

theorem rdMask_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (bit : slot s.mem B sMask ≤ 1) :
    WP isa (.block VG.Impl.Rsa.RISCV64.RecoverDet.mask) s fun t =>
      (t.gpr .t4 = (if decide (slot s.mem B sMask ≠ 0) then BitVec.allOnes 64 else 0) ∧ t.mem = s.mem) ∧
        Keep [.t4, .t5] s t := by
  have hz := h.hdr_le
  have nw := h.nowrap
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have hz' : sMask + 8 ≤ Z := by simp only [hdr_eq, sMask] at hz ⊢; omega_arith
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
  have lw : kOf s0 ≤ 8 * wOf s0 := by simp only [wOf]; omega_arith
  have bit : slot t.mem (bOf s0) sMask ≤ 1 := by rw [hm]; exact Bool.toNat_le b
  have Z64 : zOf s0 ≤ 2 ^ 64 := by have := h.ws; simp only [zOf]; omega_arith
  have fitZ : ∀ j < nArr, arr (wOf s0) j + 8 * wOf s0 ≤ zOf s0 := fun j hj => by
    have := Nat.le_trans (arr_end hj) h.fits.1; simp only [S] at this; omega_arith
  have wp : (s0.gpr .a0).toNat + kOf s0 ≤ 2 ^ 64 := by have := h.wp; rw [h.h1] at this; exact this
  have wq : (s0.gpr .a2).toNat + kOf s0 ≤ 2 ^ 64 := by have := h.wq; rw [h.h3] at this; exact this
  have pw : (⟨s0.gpr .a0, kOf s0⟩ : Region) ∈ s0.wr := by rw [← h.pR_eq, h.hwr]; simp
  have qw : (⟨s0.gpr .a2, kOf s0⟩ : Region) ∈ s0.wr := by rw [← h.qR_eq, h.hwr]; simp
  have ps : (⟨s0.gpr .a0, kOf s0⟩ : Region).Disjoint (sR s0) := by rw [← h.pR_eq]; exact h.ps
  have qs : (⟨s0.gpr .a2, kOf s0⟩ : Region).Disjoint (sR s0) := by rw [← h.qR_eq]; exact h.qs
  have p_q : (⟨s0.gpr .a0, kOf s0⟩ : Region).Disjoint ⟨s0.gpr .a2, kOf s0⟩ := by
    rw [← h.pR_eq, ← h.qR_eq]; exact h.pq
  have db : decide (slot t.mem (bOf s0) sMask ≠ 0) = b := by rw [hm]; cases b <;> rfl
  unfold VG.Impl.Rsa.RISCV64.RecoverDet.stores
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (rdMask_ok ws bit) fun t1 ⟨⟨m4, m1⟩, k1⟩ => ?_
  have ws1 := ws.of_keep k1
  have c1 := c.of_keep k1 m1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (storeBytes_ok ws1 (j := aP) (by decide) (by decide) c1.s3
    (by rw [c1.s2, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by decide) (by decide) (by decide) m4
    (by omega_arith) lw (fun i hi => by rw [c1.wr]; exact bytes_in pw (by omega_arith) i hi)
    (bytes_sep ps (by omega_arith)) wp) fun t2 ⟨ws2, b2, o2, k2⟩ => ?_
  have c2 := c1.of_out k2 o2 ps (by omega_arith)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (storeBytes_ok ws2 (j := aQ) (b := decide (slot t.mem (bOf s0) sMask ≠ 0)) (by decide)
    (by decide) c2.s4 (by rw [c2.s2, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by decide) (by decide)
    (by decide) (by rw [k2.gpr (by decide)]; exact m4) (by omega_arith) lw
    (fun i hi => by rw [c2.wr]; exact bytes_in qw (by omega_arith) i hi) (bytes_sep qs (by omega_arith)) wq)
    fun t3 ⟨ws3, b3, o3, k3⟩ => ?_
  have c3 := c2.of_out k3 o3 qs (by omega_arith)
  have hz3 := ws3.hdr_le
  have nw3 := ws3.nowrap
  have hM : sMask + 8 ≤ zOf s0 := by simp only [hdr_eq, sMask] at hz3 ⊢; omega_arith
  have hb : WP isa (.block [.load .d .a0 .s11 sMask]) t3 fun u =>
      (u.gpr .a0 = word t3.mem (bOf s0) sMask ∧ u.mem = t3.mem) ∧ Keep [.a0] t3 u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [ws3.s11, add_ofNat_zero', ws3.scr.al8 (d := sMask) (by omega_arith) (by decide),
      ws3.scr.ld (d := sMask) (n := 8) hM, show sMask < 2048 by decide]
  refine WP.mono hb fun u ⟨⟨ua, um⟩, ku⟩ => ?_
  have W1 : ∀ {m : Mem} {d : Nat}, wordsVal m (bOf s0) d 1 = (word m (bOf s0) d).toNat := by
    intro m d; simp [wordsVal]
  have qv : num t2.mem (bOf s0) (wOf s0) aQ = num t.mem (bOf s0) (wOf s0) aQ :=
    (wordsVal_of_out (d := arr (wOf s0) aQ) (k := wOf s0) ps o2 (fitZ _ (by decide)) Z64).trans (by rw [m1])
  have sM : slot t3.mem (bOf s0) sMask = slot t.mem (bOf s0) sMask := by
    have e := wordsVal_of_out (d := sMask) (k := 1) qs o3 (by omega_arith) Z64
    have e2 := wordsVal_of_out (d := sMask) (k := 1) ps o2 (by omega_arith) Z64
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
  ∃ q rem, (0 < m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) →
      q = dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) / m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) ∧
      rem = dOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) % m1Of (nbOf s0) (wbOf s0) (Nv s0) (deOf s0)) ∧
    Out s0 (okDE (wbOf s0) (deOf s0) && ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) &&
      (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).1)
      (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).2.1 (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).2.2 u

/-- A valid modulus is odd and at least 3. -/
theorem nv_facts {s0 : State} (hmv : Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true) :
    Nv s0 % 2 = 1 ∧ 3 ≤ Nv s0 := by
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hmv
  obtain ⟨⟨⟨o, b⟩, _⟩, _⟩ := hmv
  exact ⟨o, Nat.le_trans (show 3 ≤ 2 ^ 2 by decide) (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by decide)) b)⟩

theorem valid_ok {s0 s : State} (h : PreC s0) (hmv : Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true)
    (c : CB s0 s0.mem s) : WP isa VG.Impl.Rsa.RISCV64.RecoverDet.valid s (VP s0) := by
  have three := (nv_facts hmv).2
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
  refine WP.mono (stA_ok h three d4) fun t5 s5 => ?_
  refine WP.mono (stB_ok h s5) fun t6 ⟨q, rem, d6⟩ => ?_
  exact WP.mono (stores_ok h d6.cb d6.ws d6.mask d6.p d6.q) fun u o => ⟨q, rem, d6.div, o⟩

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
  obtain ⟨q, rem, hdiv, o⟩ := vp
  have ⟨b8, bde, bw, bwe, nk⟩ := bounds h
  have ⟨odd, three⟩ := nv_facts hmv
  have mc := VG.Proof.Rsa.RecoverDet.model_correct (nb := nbOf s0) (wb := wbOf s0) (e := Ev s0) (d := Dv s0)
    (q := q) (rem := rem) odd three b8 bde bw bwe hdiv
  unfold VG.Proof.Rsa.RecoverDet.result at mc
  generalize (okDE (wbOf s0) (deOf s0) && ltOf (nbOf s0) (wbOf s0) (Nv s0) (deOf s0) &&
    (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).1) = b at o mc
  generalize (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).2.1 = P at o mc
  generalize (stage2 (nbOf s0) (wbOf s0) (Nv s0) q rem).2.2 = Q at o mc
  unfold fnPost
  rw [pkd_eq]
  simp only [hmv, ↓reduceIte]
  rw [← mc]
  have e8 : (256 : Nat) ^ kOf s0 = 2 ^ (8 * kOf s0) := by rw [Nat.pow_mul]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none, Spec.Rsa.writtenAll, hm]
    refine ⟨?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, ha, o.a0]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rw [o.p, o.q]
      simp
  · simp only [↓reduceIte] at mc
    have pq := VG.Proof.Rsa.RecoverDet.recoverDet_mul mc.symm
    have P1 : 1 ≤ P := by
      rcases Nat.eq_zero_or_pos P with h0 | h0
      · rw [h0, Nat.zero_mul] at pq; omega_arith
      · exact h0
    have Q1 : 1 ≤ Q := by
      rcases Nat.eq_zero_or_pos Q with h0 | h0
      · rw [h0, Nat.mul_zero] at pq; omega_arith
      · exact h0
    have hP : P < 256 ^ kOf s0 := by
      rw [e8]; have := Nat.le_mul_of_pos_right P Q1; omega_arith
    have hQ : Q < 256 ^ kOf s0 := by
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

theorem rd_correct (s : State) (hpre : (Spec.Rsa.recoverPrimesDetContract RISCV64.abi).pre s) :
    ∃ tr t, Exec isa VG.Impl.Rsa.RISCV64.RecoverDet.code s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  show WP isa VG.Impl.Rsa.RISCV64.RecoverDet.code s fun t => abiPreserved s t ∧ fnPost s t
  have h := preC_of hpre
  refine WP.mono (WP.rdwr (Q := fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra ∧
    fnPost s t) ?_) fun t ⟨⟨hp, hra, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  unfold VG.Impl.Rsa.RISCV64.RecoverDet.code
  rw [WP.seq_iff]
  refine WP.mono (entry_ok h) fun e c => ?_
  rw [WP.seq_iff]
  refine WP.mono (nCheck_ok h c) fun t ⟨t0, tm, kt⟩ => ?_
  have ct := c.of_keep kt tm
  rw [WP.seq_iff]
  refine WP.ite _ (Steps.eval_zero t .s0) (fun hz => ?_) (fun hz => ?_)
  · have hz' : t.gpr .s0 = 0 := by simpa using hz
    have hv := t0.mp hz'
    refine WP.mono (valid_ok h hv ct) fun u vp => ?_
    obtain ⟨_, _, _, o⟩ := id vp
    exact WP.mono (restore_ok' h o.ce) fun v ⟨vp', vra, vm, va⟩ => ⟨vp', vra, post_valid h hv vp vm va⟩
  · have hz' : t.gpr .s0 ≠ 0 := by simpa using hz
    have hv : ¬ Spec.Rsa.modulusValid (Nv s) (kOf s) = true := fun e => hz' (t0.mpr e)
    refine WP.mono (fail_ok h ct) fun u ⟨ce, hw⟩ => ?_
    exact WP.mono (restore_ok' h ce) fun v ⟨vp', vra, vm, va⟩ => ⟨vp', vra, post_fail hv hw vm va⟩

end VG.Proof.Rsa.RISCV64.RecDet
