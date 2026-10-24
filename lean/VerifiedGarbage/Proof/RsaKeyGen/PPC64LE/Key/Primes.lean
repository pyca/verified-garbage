module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env3
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_keygen_key` on PPC64LE: the primes

`primes_ok`: `p` and `q` ordered (`p ≥ q`), and `p - 1` and `q - 1`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy sub3 sel aZero)
open VG.Impl.RsaKeyGen.PPC64LE.Key (nArr aDv aT aOne aP0 aQ0 aP aQ aPm aQm X0 ltS primes)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- `a - 1`, or 0 for 0, from the borrow of `a - 1`. -/
theorem pred_sel {w a : Nat} (ha : a < 2 ^ (32 * w)) : (if a < 1 then 0 else subW w a 1) = a - 1 := by
  by_cases h : a < 1
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]
    unfold subW
    rw [show a + 2 ^ (32 * w) - 1 = (a - 1) + 2 ^ (32 * w) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

section
variable {s : State} {B : Addr} {Z w : Nat} {V F : Nat → Nat}

/-- The arrays `primes` writes. -/
abbrev primesArrs : List Nat := [aT, aP, aQ, aPm, aQm]

theorem primes_eq : primes = seqs (ltS X0 aP0 aQ0 ++ ([sel aP aP0 aQ0 X0, sel aQ aQ0 aP0 X0] ++
    (ltS X0 aP aOne ++ ([sel aPm aT aZero X0] ++ (ltS X0 aQ aOne ++ [sel aQm aT aZero X0]))))) := rfl

theorem primes_ok (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) (one : V aOne = 1) (zero : V aZero = 0) :
    WP isa primes s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ j < nArr, j ∉ primesArrs → V' j = V j) ∧
        (∀ d ∈ flags, d ≠ X0 → F' d = F d) ∧
        V' aP = (if V aP0 < V aQ0 then V aQ0 else V aP0) ∧ V' aQ = (if V aP0 < V aQ0 then V aP0 else V aQ0) ∧
        V' aPm = V' aP - 1 ∧ V' aQm = V' aQ - 1) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  rw [primes_eq, wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE h ks (d := X0) (a := aP0) (b := aQ0)) fun t1 ⟨h1, k1, f1, r1⟩ => ?_
  obtain ⟨V1, k1, e1, o1⟩ := k1.vx
  obtain ⟨F1, k1, g1, p1⟩ := k1.fx
  rw [wp_seqs_append (by simp) (by simp [ltS])]
  change WP isa (.seq (sel aP aP0 aQ0 X0) (sel aQ aQ0 aP0 X0)) t1 _
  refine WP.seq (WP.mono (selE h1 k1 (o := aP) (a := aP0) (b := aQ0) (sl := X0) (bit := by rw [g1]; exact flag01 _))
    fun t2 ⟨h2, k2, f2, r2⟩ => ?_)
  obtain ⟨V2, k2, e2, o2⟩ := k2.vx
  refine WP.mono (selE h2 k2 (o := aQ) (a := aQ0) (b := aP0) (sl := X0) (bit := by rw [g1]; exact flag01 _))
    fun t3 ⟨h3, k3, f3, r3⟩ => ?_
  obtain ⟨V3, k3, e3, o3⟩ := k3.vx
  rw [wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE h3 k3 (d := X0) (a := aP) (b := aOne)) fun t4 ⟨h4, k4, f4, r4⟩ => ?_
  obtain ⟨V4, k4, e4, o4⟩ := k4.vx
  obtain ⟨F4, k4, g4, p4⟩ := k4.fx
  rw [wp_seqs_append (by simp) (by simp [ltS])]
  change WP isa (sel aPm aT aZero X0) t4 _
  refine WP.mono (selE h4 k4 (o := aPm) (a := aT) (b := aZero) (sl := X0) (bit := by rw [g4]; exact flag01 _))
    fun t5 ⟨h5, k5, f5, r5⟩ => ?_
  obtain ⟨V5, k5, e5, o5⟩ := k5.vx
  rw [wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE h5 k5 (d := X0) (a := aQ) (b := aOne)) fun t6 ⟨h6, k6, f6, r6⟩ => ?_
  obtain ⟨V6, k6, e6, o6⟩ := k6.vx
  obtain ⟨F6, k6, g6, p6⟩ := k6.fx
  change WP isa (sel aQm aT aZero X0) t6 _
  refine WP.mono (selE h6 k6 (o := aQm) (a := aT) (b := aZero) (sl := X0) (bit := by rw [g6]; exact flag01 _))
    fun t ⟨ht, kt, ft, rt⟩ => ?_
  obtain ⟨V7, kt, e7, o7⟩ := kt.vx
  have hp := ks.lt (j := aP0) (by decide)
  have hq := ks.lt (j := aQ0) (by decide)
  have vP : V7 aP = if V aP0 < V aQ0 then V aQ0 else V aP0 := by
    simp (disch := decide) only [o7, o6, o5, o4, o3, e2, g1, o1]
    split <;> simp_all
  have vQ : V7 aQ = if V aP0 < V aQ0 then V aP0 else V aQ0 := by
    simp (disch := decide) only [o7, o6, o5, o4, e3, g1, o2, o1]
    split <;> simp_all
  refine ⟨ht, ⟨V7, F6, kt, fun j hj hn => ?_, fun d _ hd => ?_, vP, vQ, ?_, ?_⟩,
    ((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans ft),
    ((((((r1.trans' r2).trans' r3).trans' r4).trans' r5).trans' r6).trans' rt).mono⟩
  · simp only [primesArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n1, n2, n3, n4, n5⟩ := hn
    rw [o7 j n5, o6 j n1, o5 j n4, o4 j n1, o3 j n3, o2 j n2, o1 j n1]
  · rw [p6 d hd, p4 d hd, p1 d hd]
  · have hP : (if V aP0 < V aQ0 then V aQ0 else V aP0) < 2 ^ (32 * w) := by split <;> assumption
    rw [vP]
    vsimp [o7, o6, o5, o4, o3, o2, o1, e7, e6, e5, e4, e3, e2, e1, g6, g4, g1, zero, one, sel_flag]
    exact pred_sel hP
  · have hQ : (if V aP0 < V aQ0 then V aP0 else V aQ0) < 2 ^ (32 * w) := by split <;> assumption
    rw [vQ]
    vsimp [o7, o6, o5, o4, o3, o2, o1, e7, e6, e5, e4, e3, e2, e1, g6, g4, g1, zero, one, sel_flag]
    exact pred_sel hQ

end

end VG.Proof.RsaKeyGen.PPC64LE.Key
