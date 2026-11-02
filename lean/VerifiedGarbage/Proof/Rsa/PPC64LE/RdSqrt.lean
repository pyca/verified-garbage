module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdSquare
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
open VG.Proof.Rsa.RecoverDet (wsub sqrtStep sqrtStep_code two_div_le)
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

end

end VG.Proof.Rsa.PPC64LE.RecDet
