module
-- separate module: builds in parallel with the constant time of the entry and the check (`RdCT1.lean`)

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdTwos
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdGcd
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdProd
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdDiv
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdSquare
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdSqrt
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdContract
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvEntry
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCheck
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFail
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFinS
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvNumbers
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvLoads
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCorrect
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCandSet
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: correctness

`det_ok`: from `n` (narrow) and `d e` (wide), the stages (`RdTwos.lean` to
`RdSqrt.lean`) leave in arrays 5 and 6 and in `Recover.sMask` the factors
and mask of `RecoverDet.result`, with the quotient and remainder of the second
division where its divisor is positive.

`valid_ok`: for a valid modulus, the loads, `d e`, Appendix C.2 (`det_ok`)
and the stores write the factors of `RecoverDet.result`, which is
`Spec.Rsa.recoverDet`'s (`RecoverDet.model_correct`); `rd_correct`: the code
meets `rdP`'s postcondition (`primesKeyDet`) and the calling convention.
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

/-- The bytes of a factor. -/
abbrev outB (b : Bool) (v k : Nat) : List Byte := if b then Spec.Rsa.i2osp v k else List.replicate k 0

theorem nV_lt256 (s0 : State) : nV s0 < 256 ^ kK s0 := by
  have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kK s0))
  rwa [VG.Proof.Bignum.bytesAt_length] at this

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



open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Proof.Rsa (b2n)
open VG.Proof.Rsa.RecoverDet
open VG.Spec.Rsa (recoverDet primesKeyDet)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The arrays after `d e`: zero and `d e` (wide), `n` (narrow). -/
def A0 (s0 : State) : Bool → Nat → Nat :=
  upd (upd (upd (fun _ _ => 0) true 0 0) true 3 (dV s0 * eV s0)) false 32 (nV s0)

/-- After the loads and `d e`. -/
theorem prodD_ok {s0 t : State} (l : LdD s0 t) :
    WP isa VG.Impl.Rsa.PPC64LE.Recover.prod t fun u =>
      DS s0 true (A0 s0) [(true, 0), (true, 3), (false, 32)] (fun _ => 0) [] u := by
  have z := l.base.sz
  have h44 : sv (kK s0) = arr (ww (kK s0)) 44 := z.svw
  have := z.svZ; have := z.nw
  refine WP.mono (prod_ok l) fun u ⟨w2, kk, vM, vZ, k2⟩ => ?_
  have fits : arr (vw s0 true) 22 ≤ rvZ s0 := by
    rw [vw_wide, arr_wide]; show arr (ww (kK s0)) 44 ≤ _; omega
  refine ⟨l.base.of_keep (w := wW (kK s0)) kk (fun j hj => ?_) (fun d hd => ?_) k2, ⟨w2.scr, fits, w2.wpos, w2.wle,
    w2.r29, w2.r30, w2.r31⟩, (k2.gpr _ (by decide)).trans l.r21, (k2.gpr _ (by decide)).trans l.r23,
    (k2.gpr _ (by decide)).trans l.r25, fun e he => ?_, by decide, by simp, by simp⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    have : j < 16 := by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact Nat.le_trans (VG.Proof.Rsa.KeyWorkspace.arr_end this) z.svW
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · simp only [A0, vw_true]
      show num u.mem _ _ VG.Impl.Rsa.PPC64LE.Recover.wZ = _; rw [vZ]; rd_simp
    · simp only [A0, vw_true]
      show num u.mem _ _ VG.Impl.Rsa.PPC64LE.Recover.wM = _; rw [vM]; rd_simp
    · simp only [A0, vw_false]
      have hA9 : arr (wW (kK s0)) 9 = arr (ww (kK s0)) 18 := arrW9 _
      have e44 := VG.Proof.Rsa.KeyWorkspace.arr_end (w := ww (kK s0)) (show 32 < 44 by decide)
      simp only [num]
      rw [keepW_far kk (by decide) (by decide)
        (by rw [hA9]; exact VG.Proof.Rsa.KeyWorkspace.arr_mono (by decide)) (by simp only [S] at e44; omega)]
      rd_simp
      exact l.vN

/-- The bounds `RecoverDet.model_correct` needs, from the contract and the modulus. -/
theorem bounds {s0 : State} (h : rdP.pre s0) :
    8 * (nV s0 + 2) ≤ 2 ^ (32 * ww (kK s0)) ∧ dV s0 * eV s0 < 2 ^ (32 * ww (kK s0)) ∧
      2 * (32 * ww (kK s0)) ≤ 32 * wW (kK s0) ∧ (32 * wW (kK s0)) % 2 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, -, -, -, e8, -, d2,
    -⟩ := id h
  have hkK : kK s0 = (s0.gpr .r8).toNat := rfl
  have h8 : 8 * kK s0 + 64 ≤ 32 * ww (kK s0) := by simp only [ww]; omega
  have bD : dV s0 < 2 ^ (8 * kK s0) := by
    have := os2ip_lt8 (dB s0); simp only [dB, Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  have bE : eV s0 < 2 ^ 64 := by
    have := os2ip_lt8 (eB s0); simp only [eB, Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  have bN : nV s0 < 2 ^ (8 * kK s0) := by
    have := nV_lt256 s0; rwa [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  have p4 : 2 ^ (8 * kK s0 + 4) ≤ 2 ^ (32 * ww (kK s0)) := Nat.pow_le_pow_right (by decide) (by omega)
  have p64 : 2 ^ (8 * kK s0 + 64) ≤ 2 ^ (32 * ww (kK s0)) := Nat.pow_le_pow_right (by decide) (by omega)
  have one : 1 ≤ 2 ^ (8 * kK s0) := Nat.one_le_two_pow
  refine ⟨?_, ?_, by simp only [wW]; omega, by simp only [wW]; omega⟩
  · rw [Nat.pow_add] at p4; omega
  · calc dV s0 * eV s0 < 2 ^ (8 * kK s0) * 2 ^ 64 := Nat.mul_lt_mul'' bD bE
      _ = 2 ^ (8 * kK s0 + 64) := (Nat.pow_add _ _ _).symm
      _ ≤ _ := p64

section
variable [VG.Proof.Rsa.PPC64LE.InvLaw]

/-- For a valid modulus: Appendix C.2's factors, or zeros, written, and the mask returned. -/
theorem valid_ok {s0 t : State} (hd : rdP.pre s0) (e : REnt s0 t)
    (hmv : Spec.Rsa.modulusValid (nV s0) (kK s0) = true) :
    WP isa VG.Impl.Rsa.PPC64LE.RecoverDet.valid t fun u => RFin s0 u ∧ ∃ b P Q,
      u.gpr .r3 = BitVec.ofNat 64 (b2n b) ∧
      Spec.Rsa.bytesAt u.mem (s0.gpr .r3) (kK s0) = outB b P (kK s0) ∧
      Spec.Rsa.bytesAt u.mem (s0.gpr .r5) (kK s0) = outB b Q (kK s0) ∧
      recoverDet (nV s0) (eV s0) (dV s0) = (if b then some (P, Q) else none) := by
  have hn := NOk.of_valid hmv
  obtain ⟨b8, bde, bw, bwe⟩ := bounds hd
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.valid
  simp only [seqs]
  refine WP.seq (WP.mono (loads_ok e) fun t1 ⟨l1, _⟩ => ?_)
  refine WP.seq (WP.mono (prodD_ok l1) fun t2 h2 => ?_)
  refine WP.seq (WP.mono (det_ok h2 (by simp only [A0]; rd_simp) (by simp only [A0]; rd_simp; have := hn.big; omega))
    fun t3 ⟨A3, V3, q, rem, h3, hdiv, p5, p6, msk⟩ => ?_)
  have a3 : A0 s0 true 3 = dV s0 * eV s0 := by simp only [A0]; rd_simp
  have a32 : A0 s0 false 32 = nV s0 := by simp only [A0]; rd_simp
  simp only [a3, a32] at hdiv p5 p6 msk
  have mc := model_correct (nb := 32 * ww (kK s0)) (wb := 32 * wW (kK s0)) (q := q) (rem := rem) hn.odd
    (by have := hn.big; omega) b8 bde bw bwe hdiv
  unfold result at mc
  generalize (okDE (32 * wW (kK s0)) (dV s0 * eV s0) && ltOf (32 * ww (kK s0)) (32 * wW (kK s0)) (nV s0)
    (dV s0 * eV s0) && (stage2 (32 * ww (kK s0)) (32 * wW (kK s0)) (nV s0) q rem).1) = b at msk mc
  rw [← p5, ← p6] at mc
  have sm : slot t3.mem (rvB s0) VG.Impl.Rsa.PPC64LE.Recover.sMask = b2n b := by
    rw [h3.sl _ (by decide)]; exact msk
  have w3 : Ws t3 (rvB s0) (rvZ s0) (ww (kK s0)) VG.Impl.Rsa.PPC64LE.Recover.nArr := h3.ws
  refine WP.mono (stores_ok (h3.base.fin h3.ws.r30) w3 h3.r21 h3.r23 h3.r25 sm) fun u ⟨fu, r3, bp, bq⟩ =>
    ⟨fu, b, A3 false 5, A3 false 6, r3, ?_, ?_, mc.symm⟩
  all_goals
    have hk : kK s0 ≤ 4 * ww (kK s0) := by simp only [ww]; omega
    have e8 : (2 : Nat) ^ (8 * kK s0) = 256 ^ kK s0 := by rw [Nat.pow_mul]
    have nl := nV_lt256 s0
  · cases b
    · exact CrtValues.bytes_zero fun c hc => by rw [bp c hc]; rfl
    · simp only [ite_true] at mc
      have pq := recoverDet_mul mc.symm
      have v5 := h3.val (b' := false) (j := 5) (by decide)
      rw [vw_false] at v5
      have Q1 : 1 ≤ A3 false 6 := by
        rcases Nat.eq_zero_or_pos (A3 false 6) with h0 | h0
        · rw [h0, Nat.mul_zero] at pq; have := hn.big; omega
        · exact h0
      have hP : A3 false 5 ≤ nV s0 := by rw [← pq]; exact Nat.le_mul_of_pos_right _ Q1
      rw [CrtValues.bytes_of hk bp, v5, e8, Nat.mod_eq_of_lt (by omega)]; rfl
  · cases b
    · exact CrtValues.bytes_zero fun c hc => by rw [bq c hc]; rfl
    · simp only [ite_true] at mc
      have pq := recoverDet_mul mc.symm
      have v6 := h3.val (b' := false) (j := 6) (by decide)
      rw [vw_false] at v6
      have P1 : 1 ≤ A3 false 5 := by
        rcases Nat.eq_zero_or_pos (A3 false 5) with h0 | h0
        · rw [h0, Nat.zero_mul] at pq; have := hn.big; omega
        · exact h0
      have hQ : A3 false 6 ≤ nV s0 := by rw [← pq]; exact Nat.le_mul_of_pos_left _ P1
      rw [CrtValues.bytes_of hk bq, v6, e8, Nat.mod_eq_of_lt (by omega)]; rfl

end

/-- `primesKeyDet` of the initial state's bytes. -/
theorem pkd_eq (s0 : State) : primesKeyDet (nB s0) (eB s0) (dB s0) =
    if Spec.Rsa.modulusValid (nV s0) (kK s0) then
      (recoverDet (nV s0) (eV s0) (dV s0)).map fun (p, q) => (Spec.Rsa.i2osp p (kK s0), Spec.Rsa.i2osp q (kK s0))
    else none := by
  have hl : (nB s0).length = kK s0 := VG.Proof.Bignum.bytesAt_length _ _ _
  unfold primesKeyDet
  rw [hl]

/-- The postcondition from the factors' bytes and the returned flag. -/
theorem rd_post_of {s0 t : State} {b : Bool} {P Q : Nat}
    (hpk : primesKeyDet (nB s0) (eB s0) (dB s0) =
      if b then some (Spec.Rsa.i2osp P (kK s0), Spec.Rsa.i2osp Q (kK s0)) else none)
    (h3 : t.gpr .r3 = BitVec.ofNat 64 (b2n b))
    (bp : Spec.Rsa.bytesAt t.mem (s0.gpr .r3) (kK s0) = outB b P (kK s0))
    (bq : Spec.Rsa.bytesAt t.mem (s0.gpr .r5) (kK s0) = outB b Q (kK s0)) : rdP.post s0 t := by
  show Spec.Rsa.writtenAll t.mem _ _ _
  rw [hpk]
  cases b
  · refine ⟨by rw [h3]; rfl, fun o ho => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact bp
    · exact bq
  · refine ⟨by rw [h3]; rfl, ?_⟩
    simp only [List.map_cons, List.map_nil]
    rw [bp, bq]; rfl

/-- The factors not found: zeros and 0. -/
theorem rd_post_none {s0 t : State} (hpk : primesKeyDet (nB s0) (eB s0) (dB s0) = none) (h3 : t.gpr .r3 = 0)
    (vp : ∀ c < kK s0, t.mem (off (s0.gpr .r3) c) = 0) (vq : ∀ c < kK s0, t.mem (off (s0.gpr .r5) c) = 0) :
    rdP.post s0 t :=
  rd_post_of (b := false) (P := 0) (Q := 0) (by rw [hpk]; rfl) (by rw [h3]; rfl) (CrtValues.bytes_zero vp)
    (CrtValues.bytes_zero vq)

section
variable [VG.Proof.Rsa.PPC64LE.InvLaw]

/-- The branch on `n`'s check. -/
theorem branchD_ok {s s2 : State} (hd : rdP.pre s) (b2 : RBase s s2) (a2 : RArgs s s2)
    (e2 : REnt s s2) (hv : s2.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (nV s) (kK s) = true) :
    WP isa (.ite (.zero .d .r0) VG.Impl.Rsa.PPC64LE.RecoverDet.valid VG.Impl.Rsa.PPC64LE.Recover.fail) s2
      fun t => RFin s t ∧ rdP.post s t := by
  refine WP.ite (s2.gpr .r0 == 0) (eval_zero s2 .r0) (fun hz => ?_) (fun hz => ?_)
  · have hmv : Spec.Rsa.modulusValid (nV s) (kK s) = true := hv.mp (beq_iff_eq.mp hz)
    refine WP.mono (valid_ok hd e2 hmv) fun t ⟨ft, b, P, Q, r3, bp, bq, rec⟩ => ⟨ft, rd_post_of ?_ r3 bp bq⟩
    rw [pkd_eq, ite_eq_left hmv, rec]
    cases b <;> rfl
  · have hmv : ¬ Spec.Rsa.modulusValid (nV s) (kK s) = true := fun h' => by
      rw [hv.mpr h'] at hz; exact absurd hz (by decide)
    refine WP.mono (fail_ok (b2.fin e2.r30) a2.r21 a2.r23 a2.r25) fun t ⟨ft, t3, vp, vq, _⟩ =>
      ⟨ft, rd_post_none ?_ t3 vp vq⟩
    rw [pkd_eq, ite_eq_right hmv]

/-- All registers but `r1`, `r2` and `r13`. -/
abbrev rdRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17,
  .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem rd_correct (s : State) (h : rdP.pre s) :
    ∃ tr t, Exec isa VG.Impl.Rsa.PPC64LE.RecoverDet.code s tr t ∧ abiPreserved s t ∧ rdP.post s t := by
  have hv := rdP_pre h
  show WP isa VG.Impl.Rsa.PPC64LE.RecoverDet.code s fun t => abiPreserved s t ∧ rdP.post s t
  have hw := WP.keep rdRegs (c := VG.Impl.Rsa.PPC64LE.RecoverDet.code) (s := s) (Q := fun t => t.sp = s.sp ∧
    t.lr = s.lr ∧ (∀ r ∈ preserved, r ≠ .r2 → t.gpr r = s.gpr r) ∧ rdP.post s t) ?_ (by decide +kernel)
    (by decide +kernel)
  · refine WP.mono hw fun t ⟨⟨tsp, tlr, hr, post⟩, kt⟩ => ⟨⟨fun r hr' => ?_, tsp, tlr⟩, post⟩
    by_cases e : r = .r2
    · subst e; exact kt.gpr (r := .r2) (by decide)
    · exact hr r hr' e
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.code
  refine WP.seq (WP.mono (entry_ok hv) fun s1 e1 => ?_)
  refine WP.seq (WP.mono (nCheck_ok e1.base e1.args) fun s2 ⟨⟨b2, a2, hv'⟩, m2, k2⟩ => ?_)
  have e2 : REnt s s2 := ⟨b2, a2, (k2.gpr _ (by decide)).trans e1.r29, (k2.gpr _ (by decide)).trans e1.r30,
    m2.trans e1.mem, (e1.keep.trans k2).mono⟩
  rw [show Spec.Rsa.os2ip (nB0 s) = nV s from rfl] at hv'
  refine WP.seq (WP.mono (branchD_ok h b2 a2 e2 hv') fun t ⟨ft, post⟩ => ?_)
  refine WP.mono (restore_ok ft) fun u ⟨⟨⟨u14, u15, u16, u17, u18, u19, u20, u21, u22, u23, u24, u25, u26, u27,
    u28, u29, u30, u31⟩, um⟩, ku⟩ => ⟨ku.sp.trans ft.sp, ku.lr.trans ft.lr, fun r hr hr2 => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> first | exact absurd rfl hr2 | with_reducible assumption
  · have e3 : u.gpr .r3 = t.gpr .r3 := ku.gpr _ (by decide)
    show Spec.Rsa.writtenAll u.mem _ _ _
    rw [um, e3]
    exact post

end

end VG.Proof.Rsa.PPC64LE.RecDet
