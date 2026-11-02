module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdSqrt
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: Appendix C.2's computation

`det_ok`: from `n` (narrow) and `d e` (wide), the factors in arrays 5 and 6
and the mask in `Recover.sMask` are those of `RecoverDet.result`, with the
quotient and remainder of the second division where its divisor is positive.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RecDet

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Proof.Rsa (b2n)
open VG.Proof.Rsa.RecoverDet
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.RecoverDet (det sB0 sB1 sLt sExact sC1 sC2 sOk5)

theorem mask_eq (c0 c1 c2 c3 c4 c5 c6 : Bool) :
    ((((((!c0 && !c1) && c2) && c3) && !c4) && !c5) && c6) = (!(c0 || c1) && c2 && (c3 && !(c4 || c5) && c6)) := by
  revert c0 c1 c2 c3 c4 c5 c6; decide

theorem b2n_dec (p : Prop) [Decidable p] : (if p then 1 else 0) = b2n (decide p) := by
  simp only [b2n, decide_eq_true_eq]

section
variable [VG.Proof.Rsa.PPC64LE.InvLaw] {s0 s : State} {A : Bool → Nat → Nat} {V : Nat → Nat}

/-- Appendix C.2, from `n` (narrow array 32) and `d e` (wide array 3). -/
theorem det_ok (h : DS s0 true A [(true, 0), (true, 3), (false, 32)] V [] s) (z : A true 0 = 0)
    (three : 3 ≤ A false 32) :
    WP isa det s fun t => ∃ A' V' q rem,
      DS s0 false A' [(false, 5), (false, 6)] V' [VG.Impl.Rsa.PPC64LE.Recover.sMask] t ∧
      (0 < m1Of (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) →
        q = dOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) /
            m1Of (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) ∧
          rem = dOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) %
            m1Of (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3)) ∧
      A' false 5 = (stage2 (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) q rem).2.1 ∧
      A' false 6 = (stage2 (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) q rem).2.2 ∧
      V' VG.Impl.Rsa.PPC64LE.Recover.sMask = b2n (okDE (32 * wW (kK s0)) (A true 3) &&
        ltOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) &&
        (stage2 (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) q rem).1) := by
  have w1 := h.base.sz.w1
  have nlo := h.lt (b' := false) (j := 32) (by decide)
  rw [vw_false] at nlo
  unfold det
  simp only [seqs]
  -- `d e - 1`, and the halvings.
  refine WP.seq (WP.mono (deMinus_ok h z) fun s1 ⟨A1, V1, h1, a15, a10, a9, a32, vb0, vb1⟩ => ?_)
  rw [vw_true] at a10 vb1
  refine WP.seq (WP.mono (twos_ok h1 a15) fun s2 ⟨A2, V2, h2, e2, b15, b8, b9, b32, b42, wb0, wb1⟩ => ?_)
  rw [a10, a32, vw_true] at e2
  rw [a9] at b9
  rw [a32] at b32
  have tw : twosOut (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) = (A2 true 14, A2 true 13, A2 true 12) :=
    e2.symm
  -- `u` odd, and both below `2^(32 w)`.
  have nm1 : wsub (32 * ww (kK s0)) (A false 32) 1 = A false 32 - 1 := wsub_of_le nlo (by omega)
  have xlt : deX (32 * wW (kK s0)) (A true 3) % 2 ^ (32 * ww (kK s0)) < 2 ^ (32 * wW (kK s0)) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide)
      (show 32 * ww (kK s0) ≤ 32 * (2 * ww (kK s0) + 2) by omega))
  have uodd : A2 true 14 % 2 = 1 := by
    have p := (twos_proj (32 * wW (kK s0)) (32 * ww (kK s0)) (A false 32 - 1)
      (deX (32 * wW (kK s0)) (A true 3) % 2 ^ (32 * ww (kK s0))) (deX (32 * wW (kK s0)) (A true 3))
      (deX (32 * wW (kK s0)) (A true 3) % 2 ^ (32 * ww (kK s0)))).1
    have i := (twos_iter (b := 32 * wW (kK s0)) (N := A false 32 - 1) (k := 32 * ww (kK s0)) (by omega)
      (by omega) xlt).1
    rw [nm1] at e2
    have := congrArg Prod.fst e2
    simp only at this
    rw [this, p]; exact i
  have bnd := twos_le (32 * wW (kK s0)) (32 * ww (kK s0)) (wsub (32 * ww (kK s0)) (A false 32) 1,
    deX (32 * wW (kK s0)) (A true 3) % 2 ^ (32 * ww (kK s0)), deX (32 * wW (kK s0)) (A true 3))
  rw [← e2] at bnd
  simp only at bnd
  have ulo : A2 true 14 < 2 ^ (32 * ww (kK s0)) := by omega
  have xlo : A2 true 13 < 2 ^ (32 * ww (kK s0)) :=
    Nat.lt_of_le_of_lt bnd.2 (Nat.mod_lt _ (Nat.two_pow_pos _))
  -- The GCD and the product.
  refine WP.seq (WP.mono (gcd_ok h2 uodd ulo xlo b8 b42) fun s3 ⟨A3, V3, h3, g8, g12, g15, g9, g32, gb0, gb1⟩ =>
    ?_)
  refine WP.seq (WP.mono (aProduct_ok h3 (by rw [g15, b15])) fun s4 ⟨A4, V4, h4, p17, p15, p9, p32, pb0, pb1⟩ =>
    ?_)
  rw [g8, g12, vw_true] at p17
  have ha : A4 true 17 = aOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) := by
    rw [p17, aOf, tw]
  -- `m`, `r`, and the second division.
  have n4 : A4 false 32 = A false 32 := by rw [p32, g32, b32]
  refine WP.seq (WP.mono (divA_ok h4 p15 (by rw [n4]; omega))
    fun s5 ⟨A5, V5, h5, m5, r5, n5, z5, o5, nn5, vlt, db0, db1⟩ => ?_)
  rw [n4, ha] at m5 r5 vlt
  rw [n4] at n5 nn5
  refine WP.seq (WP.mono (divB_ok h5 z5) fun s6 ⟨Q, R, A6, V6, h6, qr, q6, n6, z6, nW6, zz6, o6, nn6, vex, vlt6, eb0,
    eb1⟩ => ?_)
  rw [m5, r5, nn5] at qr
  -- `b`, `b²` and `b² - 4 n`.
  refine WP.seq (WP.mono (square_ok h6 zz6 n6) fun s7 ⟨A7, V7, h7, b7, sq7, z7, o7, nW7, v7⟩ => ?_)
  refine WP.seq (WP.mono (minus4n_ok h7) fun s8 ⟨A8, V8, h8, x8, z8, b8', vc1, vc2, v8⟩ => ?_)
  rw [sq7, nW7, nW6, n5, q6, vw_true] at x8 vc1
  rw [sq7, nW7, nW6, n5, q6, o7, o6, o5, p9, g9, b9, vw_true] at vc2
  rw [b7, q6] at b8'
  -- The square root and the factors.
  refine WP.seq (WP.mono (sqrt_ok h8 (by rw [z8, z7])) fun s9 ⟨A9, V9, h9, y9, b9', z9, vok, v9⟩ => ?_)
  rw [x8] at y9 vok
  rw [b8'] at b9'
  have K : 32 * wW (kK s0) / 2 = 32 * ww (kK s0) + 32 := by show 32 * (2 * ww (kK s0) + 2) / 2 = _; omega
  refine WP.mono (factors_ok h9 z9 (c0 := decide (A true 3 < 1)) (c1 := decide (deX (32 * wW (kK s0)) (A true 3) < 1))
    (c2 := decide (aOf (32 * ww (kK s0)) (32 * wW (kK s0)) (A false 32) (A true 3) / A false 32 < A false 32))
    (c3 := decide (R = 0))
    (c4 := decide (((prodStep (32 * wW (kK s0)))^[32 * ww (kK s0)] ((Q + 1) % 2 ^ (32 * ww (kK s0)),
      (Q + 1) % 2 ^ (32 * ww (kK s0)), 0)).2.2 < fourN (32 * wW (kK s0)) (A false 32)))
    (c5 := decide (wsub (32 * wW (kK s0)) (((prodStep (32 * wW (kK s0)))^[32 * ww (kK s0)]
      ((Q + 1) % 2 ^ (32 * ww (kK s0)), (Q + 1) % 2 ^ (32 * ww (kK s0)), 0)).2.2) (fourN (32 * wW (kK s0)) (A false 32))
      < 1))
    (c6 := decide (((sqrtStep (32 * ww (kK s0)) (32 * wW (kK s0)))^[32 * ww (kK s0) + 32]
      (wsub (32 * wW (kK s0)) (((prodStep (32 * wW (kK s0)))^[32 * ww (kK s0)] ((Q + 1) % 2 ^ (32 * ww (kK s0)),
        (Q + 1) % 2 ^ (32 * ww (kK s0)), 0)).2.2) (fourN (32 * wW (kK s0)) (A false 32)), 0, 0)).2.1 = 0))
    (by rw [v9 _ (by decide), v8 _ (by decide), v7 _ (by decide), eb0, db0, pb0, gb0, wb0, vb0])
    (by rw [v9 _ (by decide), v8 _ (by decide), v7 _ (by decide), eb1, db1, pb1, gb1, wb1, vb1])
    (by rw [v9 _ (by decide), v8 _ (by decide), v7 _ (by decide), vlt6, vlt])
    (by rw [v9 _ (by decide), v8 _ (by decide), v7 _ (by decide), vex])
    (by rw [v9 _ (by decide), vc1])
    (by rw [v9 _ (by decide), vc2])
    vok) fun t ⟨A10, V10, h10, p10, q10, m10⟩ => ⟨A10, V10, Q, R, h10, ?_, ?_, ?_, ?_⟩
  · unfold m1Of dOf mOf rOf; exact qr
  · rw [p10, b9', y9]
    unfold stage2 rootOf xOf sqOf bOf
    rw [K]
  · rw [q10, b9', y9]
    unfold stage2 rootOf xOf sqOf bOf
    rw [K]
  · rw [m10, mask_eq]
    unfold okDE ltOf mOf stage2 ok4Of rootOf xOf sqOf bOf
    rw [K]

end

end VG.Proof.Rsa.PPC64LE.RecDet
