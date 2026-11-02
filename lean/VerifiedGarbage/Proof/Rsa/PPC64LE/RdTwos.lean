module
-- separate module: builds in parallel with the other stages of `det_ok` (`RdCorrect.lean`)

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
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
open VG.Impl.Rsa.PPC64LE.RecoverDet (deMinus twosInit twosBody twosFlags halfIf twos sB0 sB1 sU sX sEven sBoth)

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

theorem mod2_b2n (x : Nat) : x % 2 = b2n (decide (x % 2 = 1)) := by
  rcases Nat.mod_two_eq_zero_or_one x with e | e <;> simp [e, b2n]

/-- A halving step as the code computes it, by masks. -/
theorem twoStep_code (b u x y : Nat) : twoStep b (u, x, y) =
    (if b2n (!decide (u % 2 = 1)) = 0 then u else u / 2,
      if b2n (!decide (x % 2 = 1) && !decide (u % 2 = 1)) = 0 then x else x / 2,
      if b2n (!decide (x % 2 = 1) && !decide (u % 2 = 1)) = 0 then y else 2 * y % 2 ^ b) := by
  unfold twoStep
  rcases Nat.mod_two_eq_zero_or_one u with hu | hu <;> rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    simp [hu, hx, b2n]

/-- A step of the halvings. -/
theorem twosBody_ok (h : DS s0 true A twL V [sB1, sB0] s) :
    WP isa twosBody s fun t => ∃ A' V', DS s0 true A' twL V' [sB1, sB0] t ∧
      (A' true 14, A' true 13, A' true 12) = twoStep (32 * vw s0 true) (A true 14, A true 13, A true 12) ∧
      A' true 15 = A true 15 ∧ A' true 8 = A true 8 ∧ A' true 9 = A true 9 ∧ A' false 32 = A false 32 ∧
      A' false 42 = A false 42 ∧ V' sB0 = V sB0 ∧ V' sB1 = V sB1 ∧
      t.gpr .r27 = s.gpr .r27 - BitVec.ofNat 64 1 := by
  unfold twosBody halfIf
  simp only [seqs]
  refine WP.seq ?_
  unfold twosFlags
  rw [List.append_assoc]
  refine h.bitOf (j := 14) (sl := sU) (by decide) (by decide) (ls' := [sB1, sB0]) (by decide) fun t1 h1 k1 => ?_
  refine h1.bitOf (j := 13) (sl := sX) (by decide) (by decide) (ls' := [sU, sB1, sB0]) (by decide)
    fun t2 h2 k2 => ?_
  refine WP.mono (h2.twosTail (cu := decide (A true 14 % 2 = 1)) (cx := decide (A true 13 % 2 = 1))
    (by decide) (by decide) (by simp [updV, sU, sX, ← mod2_b2n]) (by simp [updV, ← mod2_b2n])
    (ls' := [sX, sU, sB1, sB0]) (by decide)) fun s1 ⟨h3, k3⟩ => ?_
  -- `u` halved if even.
  refine WP.seq ?_
  refine WP.seq (WP.mono (h3.copy (o := 11) (a := 14) (by decide) (by decide) (by decide) (live' := twL)
    (by decide)) fun s2 ⟨h4, k4, _⟩ => ?_)
  refine WP.seq (WP.mono (h4.li9 (v := 0) (by decide)) fun s3 ⟨h5, r5, k5⟩ => ?_)
  refine WP.seq (WP.mono (h5.half (j := 11) (by decide) r5 (live' := twL) (by decide)) fun s4 ⟨h6, k6⟩ => ?_)
  refine WP.mono (h6.sel (o := 14) (a := 14) (c := 11) (sl := sEven) (by decide) (by decide) (by decide)
    (by decide) (by rd_simp)
    (live' := [(true, 11), (true, 13), (true, 12), (true, 15), (true, 8), (true, 9), (false, 32), (false, 42)])
    (by decide)) fun s5 ⟨h7, k7⟩ => ?_
  -- `x` halved if both are even.
  refine WP.seq ?_
  refine WP.seq (WP.mono (h7.copy (o := 11) (a := 13) (by decide) (by decide) (by decide) (live' := twL)
    (by decide)) fun s6 ⟨h8, k8, _⟩ => ?_)
  refine WP.seq (WP.mono (h8.li9 (v := 0) (by decide)) fun s7 ⟨h9, r9, k9⟩ => ?_)
  refine WP.seq (WP.mono (h9.half (j := 11) (by decide) r9 (live' := twL) (by decide)) fun s8 ⟨h10, k10⟩ => ?_)
  refine WP.mono (h10.sel (o := 13) (a := 13) (c := 11) (sl := sBoth) (by decide) (by decide)
    (by decide) (by decide) (by rd_simp)
    (live' := [(true, 11), (true, 14), (true, 12), (true, 15), (true, 8), (true, 9), (false, 32), (false, 42)])
    (by decide)) fun s9 ⟨h11, k11⟩ => ?_
  -- `2^k x` doubled if both are even.
  refine WP.seq (WP.mono (h11.copy (o := 11) (a := 12) (by decide) (by decide) (by decide) (live' := twL)
    (by decide)) fun s10 ⟨h12, k12, _⟩ => ?_)
  refine WP.seq (WP.mono (h12.shl (j := 11) (by decide) (live' := twL) (by decide)) fun s11 ⟨h13, _, k13⟩ => ?_)
  refine WP.seq (WP.mono (h13.sel (o := 12) (a := 12) (c := 11) (sl := sBoth) (by decide) (by decide)
    (by decide) (by decide) (by rd_simp)
    (live' := [(true, 11), (true, 14), (true, 13), (true, 15), (true, 8), (true, 9), (false, 32), (false, 42)])
    (by decide)) fun s12 ⟨h14, k14⟩ => ?_)
  refine WP.mono h14.next fun t ⟨ht, c, kt⟩ => ⟨_, _, ht.drop (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [twoStep_code]
    rd_simp
  all_goals first
    | rd_simp
    | (rw [c, k14.gpr _ (by decide), k13.gpr _ (by decide), k12.gpr _ (by decide), k11.gpr _ (by decide),
        k10.gpr _ (by decide), k9.gpr _ (by decide), k8.gpr _ (by decide), k7.gpr _ (by decide),
        k6.gpr _ (by decide), k5.gpr _ (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide),
        k2.gpr _ (by decide), k1.gpr _ (by decide)])

/-- The halvings: `32 w` steps from `(n - 1, x mod 2^(32 w), x)`. -/
theorem twos_ok (h : DS s0 true A [(true, 15), (true, 10), (true, 9), (false, 32)] V [sB1, sB0] s)
    (z : A true 15 = 0) :
    WP isa twos s fun t => ∃ A' V', DS s0 true A' twL V' [sB1, sB0] t ∧
      (A' true 14, A' true 13, A' true 12) = (twoStep (32 * vw s0 true))^[32 * ww (kK s0)]
        (wsub (32 * ww (kK s0)) (A false 32) 1, A true 10 % 2 ^ (32 * ww (kK s0)), A true 10) ∧
      A' true 15 = 0 ∧ A' true 8 = 0 ∧ A' true 9 = A true 9 ∧ A' false 32 = A false 32 ∧ A' false 42 = 1 ∧
      V' sB0 = V sB0 ∧ V' sB1 = V sB1 := by
  have w2 := h.base.sz.w2
  have w1 := h.base.sz.w1
  unfold twos
  simp only [seqs]
  refine WP.seq (WP.mono (twosInit_ok h z) fun u ⟨A1, h1, a14, a13, a12, a15, a8, a9, a32, a42, c1⟩ => ?_)
  let Inv : Nat → State → Prop := fun i t => ∃ A' V', DS s0 true A' twL V' [sB1, sB0] t ∧
    (A' true 14, A' true 13, A' true 12) = (twoStep (32 * vw s0 true))^[i]
      (wsub (32 * ww (kK s0)) (A false 32) 1, A true 10 % 2 ^ (32 * ww (kK s0)), A true 10) ∧
    A' true 15 = 0 ∧ A' true 8 = 0 ∧ A' true 9 = A true 9 ∧ A' false 32 = A false 32 ∧ A' false 42 = 1 ∧
    V' sB0 = V sB0 ∧ V' sB1 = V sB1
  refine WP.mono (VG.Proof.Bignum.PPC64LE.wp_countdown (body := twosBody) (cnt := .r27) (N := 32 * ww (kK s0))
    (by omega) (by omega) Inv (fun i _ t ⟨A', V', ht, e, z15, z8, o9, n32, o42, v0, v1⟩ _ => ?_)
    ⟨A1, V, h1, by rw [a14, a13, a12]; rfl, a15, a8, a9, a32, a42, rfl, rfl⟩ c1) fun t ht => ht
  refine WP.mono (twosBody_ok ht) fun t' ⟨A'', V'', ht', e', z15', z8', o9', n32', o42', v0', v1', c'⟩ =>
    ⟨⟨A'', V'', ht', ?_, by rw [z15', z15], by rw [z8', z8], by rw [o9', o9], by rw [n32', n32], by rw [o42', o42],
      by rw [v0', v0], by rw [v1', v1]⟩, c'⟩
  rw [e', Function.iterate_succ_apply', ← e]

end

end VG.Proof.Rsa.PPC64LE.RecDet
