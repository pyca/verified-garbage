module
-- separate module: builds in parallel with the other stages of `det_ok` (`RdCorrect.lean`)

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
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
open VG.Proof.Rsa.RecoverDet (wsub wsub_neg sqrtStep sqrtStep_code two_div_le)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.RecoverDet (sqrt sqrtBody factors sB0 sB1 sLt sExact sC1 sC2 sBb sOk5)

/-- The arrays of the square root: the radicand, the remainder, the root, `b` and zero. -/
abbrev sqL : List (Bool × Nat) := [(true, 18), (false, 2), (false, 4), (false, 25), (false, 30)]

/-- The slots the square root keeps. -/
abbrev sqS : List Nat := [sC2, sC1, sExact, sLt, sB1, sB0]

section
variable {s0 s : State} {A : Bool → Nat → Nat} {V : Nat → Nat}

theorem one_sub_ite (p : Prop) [Decidable p] : 1 - (if p then 1 else 0) = if p then 0 else 1 := by
  split <;> rfl

/-- A step of the square root. -/
theorem sqrtBody_ok (h : DS s0 false A sqL V sqS s) :
    WP isa sqrtBody s fun t => ∃ A' V', DS s0 false A' sqL V' sqS t ∧
      (A' true 18, A' false 2, A' false 4) =
        sqrtStep (32 * ww (kK s0)) (32 * wW (kK s0)) (A true 18, A false 2, A false 4) ∧
      A' false 25 = A false 25 ∧ A' false 30 = A false 30 ∧ (∀ d ∈ sqS, V' d = V d) ∧
      t.gpr .r27 = s.gpr .r27 - BitVec.ofNat 64 1 := by
  have w1 := h.base.sz.w1
  have lX := h.lt (b' := true) (j := 18) (by decide)
  have lR := h.lt (b' := false) (j := 2) (by decide)
  rw [vw_true] at lX
  rw [vw_false] at lR
  unfold sqrtBody
  simp only [seqs]
  -- The radicand's top bit into the remainder.
  refine WP.seq (WP.mono h.toWB fun s1 ⟨h1, k1⟩ => ?_)
  refine WP.seq (WP.mono (h1.shl (j := 18) (by decide) (live' := [(false, 2), (false, 4), (false, 25), (false, 30)])
    (by decide)) fun s2 ⟨h2, c2, k2⟩ => ?_)
  refine WP.seq (WP.mono h2.toNB fun s3 ⟨h3, k3⟩ => ?_)
  have c3 : (s3.gpr .r9).toNat = 2 * A true 18 / 2 ^ (32 * wW (kK s0)) := by
    rw [k3.gpr _ (by decide), c2]; rd_simp
  refine WP.seq (WP.mono (h3.shlC (j := 2) (by decide) c3 (two_div_le lX)
    (live' := [(true, 18), (false, 4), (false, 25), (false, 30)]) (by decide)) fun s4 ⟨h4, _, k4⟩ => ?_)
  -- The next bit.
  refine WP.seq (WP.mono h4.toWB fun s5 ⟨h5, k5⟩ => ?_)
  refine WP.seq (WP.mono (h5.shl (j := 18) (by decide) (live' := [(false, 2), (false, 4), (false, 25), (false, 30)])
    (by decide)) fun s6 ⟨h6, c6, k6⟩ => ?_)
  refine WP.seq (WP.mono h6.toNB fun s7 ⟨h7, k7⟩ => ?_)
  have c7 : (s7.gpr .r9).toNat = 2 * (2 * A true 18 % 2 ^ (32 * wW (kK s0))) / 2 ^ (32 * wW (kK s0)) := by
    rw [k7.gpr _ (by decide), c6]; rd_simp
  refine WP.seq (WP.mono (h7.shlC (j := 2) (by decide) c7 (two_div_le (Nat.mod_lt _ (Nat.two_pow_pos _)))
    (live' := [(true, 18), (false, 4), (false, 25), (false, 30)]) (by decide)) fun s8 ⟨h8, _, k8⟩ => ?_)
  -- `4 y + 1`.
  refine WP.seq (WP.mono (h8.copy (o := 6) (a := 4) (by decide) (by decide) (by decide) (live' := sqL)
    (by decide)) fun s9 ⟨h9, k9, _⟩ => ?_)
  refine WP.seq (WP.mono (h9.shl (j := 6) (by decide) (live' := sqL) (by decide)) fun s10 ⟨h10, _, k10⟩ => ?_)
  refine WP.seq (WP.mono (h10.li9 (v := 1) (by decide)) fun s11 ⟨h11, r11, k11⟩ => ?_)
  refine WP.seq (WP.mono (h11.shlC (j := 6) (c := 1) (by decide) (by rw [r11]; rfl) (by decide) (live' := sqL) (by decide))
    fun s12 ⟨h12, _, k12⟩ => ?_)
  -- The comparison and the new remainder.
  refine WP.seq (WP.mono (h12.sub3 (o := 8) (a := 2) (c := 6) (by decide) (by decide) (by decide)
    (live' := (false, 6) :: sqL) (by decide)) fun s13 ⟨h13, b13, k13⟩ => ?_)
  refine WP.seq (WP.mono (h13.stBorrowB (sl := sBb) (by decide) b13 (by split <;> decide) (ls' := sqS)
    (by decide)) fun s14 ⟨h14, k14⟩ => ?_)
  refine WP.seq (WP.mono (h14.sel (o := 2) (a := 8) (c := 2) (sl := sBb) (by decide) (by decide) (by decide)
    (by decide) (by rd_simp) (live' := [(true, 18), (false, 4), (false, 25), (false, 30)]) (by decide))
    fun s15 ⟨h15, k15⟩ => ?_)
  -- The root's new bit.
  refine WP.seq (WP.mono (h15.not9' (d := sBb) (by decide) (by rd_simp))
    fun s16 ⟨h16, r16, k16⟩ => ?_)
  refine WP.seq (WP.mono (h16.shlC (j := 4) (by decide) r16 (by omega)
    (live' := [(false, 2), (true, 18), (false, 25), (false, 30)]) (by decide)) fun s17 ⟨h17, _, k17⟩ => ?_)
  refine WP.mono h17.next fun t ⟨ht, c, kt⟩ => ⟨_, _, ht.drop (by decide) (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · rw [sqrtStep_code (by omega) lX]
    rd_simp
    refine ⟨?_, ?_⟩
    · simp only [← Nat.not_lt, ite_not]
    · simp only [one_sub_ite]
  · rd_simp
  · rd_simp
  · intro d hd; simp only [sqS, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> rd_simp
  · rw [c, k17.gpr _ (by decide), k16.gpr _ (by decide), k15.gpr _ (by decide), k14.gpr _ (by decide),
      k13.gpr _ (by decide), k12.gpr _ (by decide), k11.gpr _ (by decide), k10.gpr _ (by decide),
      k9.gpr _ (by decide), k8.gpr _ (by decide), k7.gpr _ (by decide), k6.gpr _ (by decide),
      k5.gpr _ (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide)]

/-- The square root: `16 W` steps from `(X, 0, 0)`, and whether the remainder is zero. -/
theorem sqrt_ok (h : DS s0 true A [(true, 18), (true, 15), (false, 25)] V sqS s) (z : A true 15 = 0) :
    WP isa sqrt s fun t => ∃ A' V', DS s0 false A' [(false, 4), (false, 25), (false, 30)] V' (sOk5 :: sqS) t ∧
      A' false 4 = ((sqrtStep (32 * ww (kK s0)) (32 * wW (kK s0)))^[32 * ww (kK s0) + 32] (A true 18, 0, 0)).2.2 ∧
      A' false 25 = A false 25 ∧ A' false 30 = 0 ∧
      V' sOk5 = b2n (decide (((sqrtStep (32 * ww (kK s0)) (32 * wW (kK s0)))^[32 * ww (kK s0) + 32]
        (A true 18, 0, 0)).2.1 = 0)) ∧ (∀ d ∈ sqS, V' d = V d) := by
  have w2 := h.base.sz.w2
  unfold sqrt
  simp only [seqs]
  refine WP.seq (WP.mono h.toNB fun s1 ⟨h1, _⟩ => ?_)
  have h1a := h1.addLow (k := 15) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (h1a.copy (o := 2) (a := 30) (by decide) (by decide) (by decide)
    (live' := [(false, 30), (true, 18), (false, 25)]) (by decide)) fun s2 ⟨h2, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.copy (o := 4) (a := 30) (by decide) (by decide) (by decide)
    (live' := [(false, 2), (false, 30), (true, 18), (false, 25)]) (by decide)) fun s3 ⟨h3, _, _⟩ => ?_)
  refine WP.seq (WP.mono h3.countS fun s4 ⟨h4, c4, _⟩ => ?_)
  let Inv : Nat → State → Prop := fun i t => ∃ A' V', DS s0 false A' sqL V' sqS t ∧
    (A' true 18, A' false 2, A' false 4) = (sqrtStep (32 * ww (kK s0)) (32 * wW (kK s0)))^[i] (A true 18, 0, 0) ∧
    A' false 25 = A false 25 ∧ A' false 30 = 0 ∧ (∀ d ∈ sqS, V' d = V d)
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.wp_countdown (body := sqrtBody) (cnt := .r27)
    (N := 32 * ww (kK s0) + 32) (by omega) (by omega) Inv (fun i _ t ⟨A', V', ht, e, b', z', v⟩ _ => ?_)
    ⟨_, _, h4.drop (by decide) (by decide), by rd_simp [z], by rd_simp, by rd_simp [z], fun _ _ => rfl⟩ c4)
    fun s5 ⟨A5, V5, h5, e5, b5, z5, v5⟩ => ?_)
  · refine WP.mono (sqrtBody_ok ht) fun t' ⟨A'', V'', ht', e', b'', z'', v', c'⟩ =>
      ⟨⟨A'', V'', ht', ?_, b''.trans b', z''.trans z', fun d hd => (v' d hd).trans (v d hd)⟩, c'⟩
    rw [e', Function.iterate_succ_apply', ← e]
  refine WP.mono (h5.eqS (d := sOk5) (a := 2) (c := 30) (by decide) (by decide) (by decide) (ls' := sqS)
    (by decide)) fun t ⟨ht, _⟩ => ⟨_, _, ht.drop (by decide) (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · have e := congrArg (fun p => p.2.2) e5; simp only at e; rw [← e]
  · rd_simp [b5]
  · rd_simp [z5]
  · have e := congrArg (fun p => p.2.1) e5; simp only at e; rw [← e]; rd_simp [z5]
  · intro d hd; simp only [sqS, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> rd_simp [v5]

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
