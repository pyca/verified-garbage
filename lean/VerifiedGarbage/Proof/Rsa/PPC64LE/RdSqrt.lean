module
-- separate module: builds in parallel with the other stages of `det_ok` (`RdCorrect.lean`)

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdSqrtW
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: the square root and the factors

`sqrt_ok`: `16 W` steps of `RecoverDet.sqrtStep` on the wide radicand and
the narrow remainder and root (`RecoverDet.sqrtStep_code`: as the code
computes a step), and whether the remainder is zero; `factors_ok`:
`p = (b + ϒ) / 2`, `q = (b - ϒ) / 2` and the mask.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RecDet

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Proof.Rsa (b2n)
open VG.Proof.Rsa.RecoverDet (wsub wsub_neg)
open VG.Spec.Rsa (isqrt)
open VG.Proof.Rsa.KeyWorkspace (arr S num)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.RecoverDet (sqrt factors sB0 sB1 sLt sExact sC1 sC2 sBb sOk5)

/-- The arrays of the square root: the radicand, the remainder, the root, `b` and zero. -/
abbrev sqL : List (Bool × Nat) := [(true, 18), (false, 2), (false, 4), (false, 25), (false, 30)]

/-- The slots the square root keeps. -/
abbrev sqS : List Nat := [sC2, sC1, sExact, sLt, sB1, sB0]

section
variable {s0 s : State} {A : Bool → Nat → Nat} {V : Nat → Nat}

/-- The square root by words (`RdSqrtW.sqrtW_ok`) of `X`, the wide radicand's low `2 H` words (`H` the words
of `n`), and whether `X` is a square; the root in the narrow array 4, `b` and zero kept. -/
theorem sqrt_ok (h : DS s0 true A [(true, 18), (true, 15), (false, 25)] V sqS s) (z : A true 15 = 0) :
    WP isa sqrt s fun t => ∃ A' V', DS s0 false A' [(false, 4), (false, 25), (false, 30)] V' (sOk5 :: sqS) t ∧
      A' false 4 = isqrt (A true 18 % 2 ^ (64 * (2 * ((kK s0 + 7) / 8)))) ∧
      A' false 25 = A false 25 ∧ A' false 30 = 0 ∧
      V' sOk5 = b2n (decide (isqrt (A true 18 % 2 ^ (64 * (2 * ((kK s0 + 7) / 8)))) *
        isqrt (A true 18 % 2 ^ (64 * (2 * ((kK s0 + 7) / 8)))) = A true 18 % 2 ^ (64 * (2 * ((kK s0 + 7) / 8))))) ∧
      (∀ d ∈ sqS, V' d = V d) := by
  have w1 := h.base.sz.w1
  have w2 := h.base.sz.w2
  obtain ⟨H, hH⟩ : ∃ H, H = (kK s0 + 7) / 8 := ⟨_, rfl⟩
  rw [← hH]
  have hwW : vw s0 true = 4 * H + 6 := by rw [vw_true, hH]; simp only [wW, ww]; omega
  have hww : vw s0 false = 2 * H + 2 := by rw [vw_false, hH]
  have hwH : ww (kK s0) = 2 * H + 2 := by rw [hH]
  have hL : vw s0 true = 2 * (2 * H + 3) := by omega
  have hz15 : num s.mem (rvB s0) (vw s0 true) 15 = 0 := by rw [h.val (by decide)]; exact z
  have eX : A true 18 % 2 ^ (64 * (2 * H)) = wordsVal s.mem (rvB s0) (arr (vw s0 true) 18) (2 * H) := by
    rw [RdSqrtW.wv_low s.mem (rvB s0) (L := 2 * H + 3) (by omega),
      ← VG.Proof.Rsa.PPC64LE.RdShift.num_words _ _ _ hL, h.val (by decide)]
  generalize hX : A true 18 % 2 ^ (64 * (2 * H)) = X at eX ⊢
  have hXlt : X < 2 ^ (64 * (2 * H)) := by rw [← hX]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  refine RdSqrtW.sqrtW_ok h.ws (by decide) (by decide) hwW (by omega) (by omega) hz15 eX
    fun t e1 e2 Wt kt rt => ?_
  have kn := keep_W_w (w := vw s0 false) kt
  have fitN : ∀ j, j < vN false → arr (vw s0 false) j + S (vw s0 false) ≤ 2 ^ 64 := fun j hj => h.fit false hj
  have n25 : num t.mem (rvB s0) (vw s0 false) 25 = A false 25 :=
    (kn.num (by decide) (by decide) (fitN 25 (by decide))).trans (h.val (by decide))
  have n30 : num t.mem (rvB s0) (vw s0 false) 30 = 0 := by
    rw [kn.num (by decide) (by decide) (fitN 30 (by decide)), vw_false, show 30 = 2 * 15 from rfl, h.low (by decide),
      z]; rfl
  have hy : isqrt X < 2 ^ (64 * H) := by
    have := VG.Proof.Rsa.RecoverDet.isqrt_sq_le X
    refine Nat.lt_of_not_le fun hc => ?_
    have := Nat.mul_le_mul hc hc
    rw [← Nat.pow_add, show 64 * H + 64 * H = 64 * (2 * H) by omega] at this
    omega
  have n4 : num t.mem (rvB s0) (vw s0 false) 4 = isqrt X := by
    rw [VG.Proof.Rsa.PPC64LE.RdShift.num_words _ _ _ (show vw s0 false = 2 * (H + 1) by omega),
      show arr (vw s0 false) 4 = arr (vw s0 true) 2 from (arr_wide _ 2).symm,
      RdSqrtW.wv_low t.mem (rvB s0) (L := 2 * H + 3) (by omega), e1]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega)))
  have ht : DS s0 true (upd (upd A false 4 (isqrt X)) false 30 0) [(false, 4), (false, 25), (false, 30)]
      (updV V sOk5 (b2n (decide (isqrt X * isqrt X = X)))) (sOk5 :: sqS) t := by
    refine ⟨h.base.of_keep kt (fun j hj => fit_sv s0 true (by simp at hj; show j < 22; omega)) (by decide) rt,
      Wt, (rt.gpr _ (by decide)).trans h.r21, (rt.gpr _ (by decide)).trans h.r23, (rt.gpr _ (by decide)).trans h.r25,
      fun e he => ?_, fun e he => ?_, fun d hd => ?_, fun d hd => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · rw [n4]; simp [upd]
      · rw [n25]; simp [upd]
      · rw [n30]; simp [upd]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [show sOk5 = 48 from rfl, e2]; simp [updV, b2n]
      all_goals
        rw [kt.slot (by decide) (by decide), h.sl _ (by decide)]
        simp [updV, sOk5, sB0, sB1, sLt, sExact, sC1, sC2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine WP.mono ht.toNB fun u ⟨hu, _⟩ => ⟨_, _, hu, by simp [upd], by simp [upd], by simp [upd], by simp [updV],
    fun d hd => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [updV, sOk5, sB0, sB1, sLt, sExact, sC1, sC2]

/-- The factors and the mask. -/
theorem factors_ok (h : DS s0 false A [(false, 4), (false, 25), (false, 30)] V (sOk5 :: sqS) s) (z : A false 30 = 0)
    {c0 c1 c2 c3 c4 c5 c6 : Bool} (v0 : V sB0 = b2n c0) (v1 : V sB1 = b2n c1) (v2 : V sLt = b2n c2)
    (v3 : V sExact = b2n c3) (v4 : V sC1 = b2n c4) (v5 : V sC2 = b2n c5) (v6 : V sOk5 = b2n c6) :
    WP isa factors s fun t => ∃ A' V', DS s0 false A' [(false, 5), (false, 6)] V' [VG.Impl.Rsa.PPC64LE.Recover.sMask] t ∧
      A' false 5 = (A false 25 + A false 4) % 2 ^ (32 * ww (kK s0)) / 2 ∧
      A' false 6 = wsub (32 * ww (kK s0)) (A false 25) (A false 4) / 2 ∧
      V' VG.Impl.Rsa.PPC64LE.Recover.sMask = b2n ((((((!c0 && !c1) && c2) && c3) && !c4) && !c5) && c6) := by
  have l25 := h.lt (b' := false) (j := 25) (by decide)
  have l4 := h.lt (b' := false) (j := 4) (by decide)
  rw [vw_false] at l25 l4
  unfold factors VG.Impl.Rsa.PPC64LE.RecoverDet.add
  simp only [seqs]
  refine WP.seq ?_
  refine WP.seq (WP.mono (h.sub3 (o := 9) (a := 30) (c := 4) (by decide) (by decide) (by decide)
    (live' := [(false, 4), (false, 25), (false, 30)]) (by decide)) fun s1 ⟨h1, _, _⟩ => ?_)
  refine WP.mono (h1.sub3 (o := 5) (a := 25) (c := 9) (by decide) (by decide) (by decide)
    (live' := [(false, 4), (false, 25)]) (by decide)) fun s2 ⟨h2, _, _⟩ => ?_
  refine WP.seq (WP.mono (h2.li9 (v := 0) (by decide)) fun s3 ⟨h3, r3, _⟩ => ?_)
  refine WP.seq (WP.mono (h3.half (j := 5) (by decide) r3 (live' := [(false, 4), (false, 25)]) (by decide))
    fun s4 ⟨h4, _⟩ => ?_)
  refine WP.seq (WP.mono (h4.sub3 (o := 6) (a := 25) (c := 4) (by decide) (by decide) (by decide)
    (live' := [(false, 5), (false, 4), (false, 25)]) (by decide)) fun s5 ⟨h5, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h5.li9 (v := 0) (by decide)) fun s6 ⟨h6, r6, _⟩ => ?_)
  refine WP.seq (WP.mono (h6.half (j := 6) (by decide) r6 (live' := [(false, 5), (false, 4), (false, 25)])
    (by decide)) fun s7 ⟨h7, _⟩ => ?_)
  refine WP.mono (h7.mask (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4) (c5 := c5) (c6 := c6)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) v0 v1 v2 v3 v4 v5 v6)
    fun t ⟨ht, _⟩ => ⟨_, _, ht.drop (by decide) (by decide), ?_, ?_, by rd_simp⟩
  · rd_simp [z]
    rw [wsub_neg l25 l4]
  · rd_simp

end

end VG.Proof.Rsa.PPC64LE.RecDet
