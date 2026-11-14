module
-- separate module: builds in parallel with the other stages of `det_ok` (`RdCorrect.lean`)

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdShift
import VerifiedGarbage.Proof.Rsa.RecoverDetWords
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: `d e - 1` and the halvings

`deMinus_ok`: one, `x = d e - 1` and the borrows; `twos_ok`: the `32 w`
halvings (`RecoverDet.twoStep`) from `(n - 1, x mod 2^(32 w), x)`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RecDet

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Proof.Rsa (b2n)
open VG.Proof.Rsa.RecoverDet (wsub deX)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.RecoverDet (twoStep)
open VG.Impl.Rsa.PPC64LE.RecoverDet (deMinus twosInit twos sB0 sB1 sUw sUb sTw sTb)
open VG.Proof.Bignum.ShiftStages (tz)

section
variable {s0 s : State} {b : Bool} {A : Bool → Nat → Nat} {live : List (Bool × Nat)} {V : Nat → Nat} {ls : List Nat}

/-- `deMinus`: one (wide), `x = d e - 1`, zero, and the borrows of `d e - 1` and `x - 1`. -/
theorem deMinus_ok (h : DS s0 true A [(true, 0), (true, 3), (false, 32)] V [] s) (z : A true 0 = 0) :
    WP isa deMinus s fun t => ∃ A' V',
      DS s0 true A' [(true, 15), (true, 10), (true, 9), (false, 32)] V' [sB1, sB0] t ∧
      A' true 15 = 0 ∧ A' true 10 = deX (32 * vw s0 true) (A true 3) ∧ A' true 9 = 1 ∧ A' false 32 = A false 32 ∧
      V' sB0 = b2n (decide (A true 3 < 1)) ∧ V' sB1 = b2n (decide (deX (32 * vw s0 true) (A true 3) < 1)) := by
  unfold deMinus
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy (o := 9) (a := 0) (by decide) (by decide) (by decide)
    (live' := [(true, 0), (true, 3), (false, 32)]) (by decide)) fun s1 ⟨h1, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.setOneB (j := 9) (by decide) (live' := [(true, 0), (true, 3), (false, 32)])
    (by decide)) fun s2 ⟨h2, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.sub3 (o := 10) (a := 3) (c := 9) (by decide) (by decide) (by decide)
    (live' := [(true, 9), (true, 0), (true, 3), (false, 32)]) (by decide)) fun s3 ⟨h3, b3, _⟩ => ?_)
  refine WP.seq (WP.mono (h3.stBorrowB (sl := sB0) (by decide) b3 (by split <;> decide) (ls' := []) (by simp))
    fun s4 ⟨h4, _⟩ => ?_)
  refine WP.seq (WP.mono (h4.sub3 (o := 11) (a := 10) (c := 9) (by decide) (by decide) (by decide)
    (live' := [(true, 10), (true, 9), (true, 0), (false, 32)]) (by decide)) fun s5 ⟨h5, b5, _⟩ => ?_)
  refine WP.seq (WP.mono (h5.stBorrowB (sl := sB1) (by decide) b5 (by split <;> decide) (ls' := [sB0])
    (by decide)) fun s6 ⟨h6, _⟩ => ?_)
  refine WP.mono (h6.copy (o := 15) (a := 0) (by decide) (by decide) (by decide)
    (live' := [(true, 10), (true, 9), (false, 32)]) (by decide)) fun t ⟨ht, _, _⟩ => ?_
  refine ⟨_, _, ht, by simp [upd, z], by simp [upd, z, deX], by simp [upd, z], by simp [upd], ?_, ?_⟩
  · simp [updV, upd, z, b2n, sB0, sB1]
  · simp [updV, upd, z, b2n, sB1, deX]

/-- `twosInit`. -/
theorem twosInit_ok (h : DS s0 true A [(true, 15), (true, 10), (true, 9), (false, 32)] V [sB1, sB0] s)
    (z : A true 15 = 0) :
    WP isa twosInit s fun t => ∃ A',
      DS s0 true A' twL V [sB1, sB0] t ∧
      A' true 14 = wsub (32 * ww (kK s0)) (A false 32) 1 ∧ A' true 13 = A true 10 % 2 ^ (32 * ww (kK s0)) ∧
      A' true 12 = A true 10 ∧ A' true 15 = 0 ∧ A' true 8 = 0 ∧ A' true 9 = A true 9 ∧
      A' false 32 = A false 32 ∧ A' false 42 = 1 ∧ t.gpr .r27 = BitVec.ofNat 64 (32 * ww (kK s0)) := by
  unfold twosInit
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy (o := 12) (a := 10) (by decide) (by decide) (by decide)
    (live' := [(true, 15), (true, 10), (true, 9), (false, 32)]) (by decide)) fun s1 ⟨h1, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.copy (o := 13) (a := 15) (by decide) (by decide) (by decide)
    (live' := [(true, 12), (true, 15), (true, 10), (true, 9), (false, 32)]) (by decide)) fun s2 ⟨h2, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.copy (o := 14) (a := 15) (by decide) (by decide) (by decide)
    (live' := [(true, 13), (true, 12), (true, 15), (true, 10), (true, 9), (false, 32)]) (by decide))
    fun s3 ⟨h3, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h3.copy (o := 8) (a := 15) (by decide) (by decide) (by decide)
    (live' := [(true, 14), (true, 13), (true, 12), (true, 15), (true, 10), (true, 9), (false, 32)]) (by decide))
    fun s4 ⟨h4, _, _⟩ => ?_)
  refine WP.seq (WP.mono h4.toNB fun s5 ⟨h5, _⟩ => ?_)
  have h5' := (h5.addLow (k := 10) (by decide) (by decide) (by decide)).addLow (k := 15) (by decide) (by decide)
    (by decide)
  refine WP.seq (WP.mono (h5'.widen (k := 13) (a := 20) (by decide) (by decide) (by simp [upd, z])
    (by decide) (by decide) (live' := [(false, 30), (true, 14), (true, 12), (true, 15), (true, 8), (true, 9),
      (false, 32)]) (by decide)) fun s6 ⟨h6, _⟩ => ?_)
  refine WP.seq (WP.mono (h6.copy (o := 42) (a := 30) (by decide) (by decide) (by decide)
    (live' := [(true, 13), (true, 14), (true, 12), (true, 15), (true, 8), (true, 9), (false, 32)]) (by decide))
    fun s7 ⟨h7, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h7.setOneB (j := 42) (by decide)
    (live' := [(true, 13), (true, 14), (true, 12), (true, 15), (true, 8), (true, 9), (false, 32)]) (by decide))
    fun s8 ⟨h8, _⟩ => ?_)
  refine WP.seq (WP.mono (h8.sub3 (o := 40) (a := 32) (c := 42) (by decide) (by decide) (by decide)
    (live' := [(false, 42), (true, 13), (true, 14), (true, 12), (true, 15), (true, 8), (true, 9), (false, 32)])
    (by decide)) fun s9 ⟨h9, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h9.widen (k := 14) (a := 40) (by decide) (by decide) (by simp [upd, z])
    (by decide) (by decide) (live' := [(false, 42), (true, 13), (true, 12), (true, 15), (true, 8), (true, 9),
      (false, 32)]) (by decide)) fun s10 ⟨h10, _⟩ => ?_)
  refine WP.block_append (WP.mono h10.countN fun s11 ⟨h11, c11, _⟩ => ?_)
  refine WP.mono h11.toWB fun t ⟨ht, kt⟩ => ⟨_, ht.drop (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [kt.gpr _ (by decide)]; exact c11⟩
  all_goals first | simp [upd, z] | simp [upd, z, vw_false]

/-- The halvings (`RecoverDet.twoStep`, `32 w` of them), for `n ≥ 2`: by the trailing zeros
of `u = n - 1` and of `u ∨ x₂` (`RecoverDetWords.twos_closed`), each array shifted once. -/
theorem twos_ok (h : DS s0 true A [(true, 15), (true, 10), (true, 9), (false, 32)] V [sB1, sB0] s)
    (z : A true 15 = 0) (n2 : 2 ≤ A false 32) :
    WP isa twos s fun t => ∃ A' V', DS s0 true A' twL V' [sB1, sB0] t ∧
      (A' true 14, A' true 13, A' true 12) = (twoStep (32 * vw s0 true))^[32 * ww (kK s0)]
        (wsub (32 * ww (kK s0)) (A false 32) 1, A true 10 % 2 ^ (32 * ww (kK s0)), A true 10) ∧
      A' true 15 = 0 ∧ A' true 8 = 0 ∧ A' true 9 = A true 9 ∧ A' false 32 = A false 32 ∧ A' false 42 = 1 ∧
      V' sB0 = V sB0 ∧ V' sB1 = V sB1 := by
  have w1 := h.base.sz.w1
  have nlt : A false 32 < 2 ^ (32 * ww (kK s0)) := by rw [← vw_false]; exact h.lt (by decide)
  have xlt : A true 10 < 2 ^ (32 * vw s0 true) := h.lt (by decide)
  have eU : wsub (32 * ww (kK s0)) (A false 32) 1 = A false 32 - 1 := by
    unfold wsub; rw [show A false 32 + 2 ^ (32 * ww (kK s0)) - 1 = A false 32 - 1 + 2 ^ (32 * ww (kK s0)) by omega_using [n2, nlt],
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [nlt])]
  generalize hU : A false 32 - 1 = U at eU
  generalize hX : A true 10 % 2 ^ (32 * ww (kK s0)) = X2
  have U0 : U ≠ 0 := by omega_using [n2, hU]
  have Ult : U < 2 ^ (32 * ww (kK s0)) := by omega_using [nlt, hU]
  have X2lt : X2 < 2 ^ (32 * ww (kK s0)) := hX ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
  -- The counts are below the words of the wide view.
  have hbw : ∀ y, y ≠ 0 → y < 2 ^ (32 * ww (kK s0)) →
      tz y / 64 < vw s0 false + 1 ∧ tz y % 64 < 64 := fun y y0 yl => by
    have := VG.Proof.Bignum.ShiftStages.tz_lt (Nat.pos_of_ne_zero y0) yl
    rw [vw_false]; exact ⟨by omega_using [this], Nat.mod_lt _ (by decide)⟩
  have UX0 : U ||| X2 ≠ 0 := fun e => U0 (Nat.or_eq_zero_iff.mp e).1
  have UXlt : U ||| X2 < 2 ^ (32 * ww (kK s0)) := Nat.or_lt_two_pow Ult X2lt
  unfold twos
  simp only [seqs]
  refine WP.seq (WP.mono (twosInit_ok h z) fun u ⟨A1, h1, a14, a13, a12, a15, a8, a9, a32, a42, _⟩ => ?_)
  rw [eU] at a14
  rw [hX] at a13
  refine WP.seq (WP.mono (RdShift.DS.tzWW h1 (a := 14) (b := 14) (sw := sUw) (sb := sUb) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [a14, Nat.or_self]; exact U0) (ls' := [sB1, sB0]) (by decide))
    fun s2 ⟨h2, _⟩ => ?_)
  refine WP.seq (WP.mono (RdShift.DS.tzWW h2 (a := 14) (b := 13) (sw := sTw) (sb := sTb) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [a14, a13]; exact UX0) (ls' := [sUb, sUw, sB1, sB0]) (by decide))
    fun s3 ⟨h3, _⟩ => ?_)
  rw [a14, Nat.or_self] at h2 h3
  rw [a13] at h3
  obtain ⟨bu1, bu2⟩ := hbw U U0 Ult
  obtain ⟨bx1, bx2⟩ := hbw _ UX0 UXlt
  refine WP.seq (WP.mono (RdShift.DS.shrByW h3 (j := 14) (sw := sUw) (sb := sUb) (by decide) (by decide)
    (by decide) (by rd_simp; exact bu1) (by rd_simp; exact bu2)
    (live' := [(true, 13), (true, 12), (true, 15), (true, 8), (true, 9), (false, 32), (false, 42)]) (by decide))
    fun s4 ⟨h4, _⟩ => ?_)
  refine WP.seq (WP.mono (RdShift.DS.shrByW h4 (j := 13) (sw := sTw) (sb := sTb) (by decide) (by decide)
    (by decide) (by rd_simp; exact bx1) (by rd_simp; exact bx2)
    (live' := [(true, 14), (true, 12), (true, 15), (true, 8), (true, 9), (false, 32), (false, 42)]) (by decide))
    fun s5 ⟨h5, _⟩ => ?_)
  refine WP.seq (WP.mono (RdShift.DS.shlByW true h5 (j := 12) (sw := sTw) (sb := sTb) (by decide) (by decide)
    (by decide) (by rd_simp; exact bx1) (fun _ => by rd_simp; exact bx2)
    (live' := [(true, 13), (true, 14), (true, 15), (true, 8), (true, 9), (false, 32), (false, 42)]) (by decide))
    fun s6 ⟨h6, _⟩ => ?_)
  refine WP.mono (h6.reg [.r27] (P := fun _ => True) (by prun [exec_li (show 0 < 2 ^ 15 by decide)]) (by decide))
    fun t ⟨ht, _, _⟩ => ⟨_, _, ht.drop (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eU, VG.Proof.Rsa.RecoverDet.twos_closed (Nat.pos_of_ne_zero U0) Ult xlt]
    rd_simp [sUw, sUb, sTw, sTb, a14, a13, a12, Nat.div_add_mod, VG.Proof.Rsa.PPC64LE.RdShift.tz_or_gcd U0]
  all_goals rd_simp [a15, a8, a9, a32, a42, sUw, sUb, sTw, sTb]


end

end VG.Proof.Rsa.PPC64LE.RecDet
