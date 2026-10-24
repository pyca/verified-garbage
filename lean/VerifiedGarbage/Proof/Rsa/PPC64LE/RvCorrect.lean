module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvRest
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvContract
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvEntry
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCheck
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvNumbers
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFail
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCorrect
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCand
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFF
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvHalving
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvLoads

/-!
# `vg_rsa_recover_primes` on PPC64LE: correctness

`rv_correct`: the code meets `rvP`'s postcondition (`primesKey`) and the
calling convention.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Spec.Rsa (recoverPrimes recoverTries splitTwos primesKey)
open VG.Impl.Rsa.PPC64LE.Recover (code valid numbers rest fail)

/-- The postcondition from the factors' bytes and the returned flag. -/
theorem post_of {s0 t : State} {b : Bool} {P Q : Nat}
    (hpk : (primesKey (nB s0) (eB s0) (dB s0)).1 =
      if b then some (Spec.Rsa.i2osp P (kK s0), Spec.Rsa.i2osp Q (kK s0)) else none)
    (h3 : t.gpr .r3 = BitVec.ofNat 64 (b2n b))
    (bp : Spec.Rsa.bytesAt t.mem (s0.gpr .r3) (kK s0) = outB b P (kK s0))
    (bq : Spec.Rsa.bytesAt t.mem (s0.gpr .r5) (kK s0) = outB b Q (kK s0)) : rvP.post s0 t := by
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

theorem pk_eq (s0 : State) : primesKey (nB s0) (eB s0) (dB s0) =
    if Spec.Rsa.modulusValid (nV s0) (kK s0) then
      match recoverPrimes (nV s0) (eV s0) (dV s0) with
      | (some (p, q), tries) => (some (Spec.Rsa.i2osp p (kK s0), Spec.Rsa.i2osp q (kK s0)), tries)
      | (none, tries) => (none, tries)
    else (none, 0) := by
  have hl : (nB s0).length = kK s0 := VG.Proof.Bignum.bytesAt_length _ _ _
  unfold primesKey
  rw [hl]; rfl

/-- The factors not found: zeros and 0. -/
theorem post_none {s0 t : State} (hpk : (primesKey (nB s0) (eB s0) (dB s0)).1 = none) (h3 : t.gpr .r3 = 0)
    (vp : ∀ c < kK s0, t.mem (off (s0.gpr .r3) c) = 0) (vq : ∀ c < kK s0, t.mem (off (s0.gpr .r5) c) = 0) :
    rvP.post s0 t :=
  post_of (b := false) (P := 0) (Q := 0) hpk (by rw [h3]; rfl) (CrtValues.bytes_zero vp) (CrtValues.bytes_zero vq)

/-- All registers but `r1`, `r2` and `r13`. -/
abbrev rvRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17,
  .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- The branch on `n`'s check. -/
theorem branch_ok {s s2 : State} (b2 : RBase s s2) (a2 : RArgs s s2)
    (e2 : REnt s s2) (hv : s2.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (nV s) (kK s) = true) :
    WP isa (.ite (.zero .d .r0) valid fail) s2 fun t => RFin s t ∧ rvP.post s t := by
  refine WP.ite (s2.gpr .r0 == 0) (eval_zero s2 .r0) (fun hz => ?_) (fun hz => ?_)
  · have hmv : Spec.Rsa.modulusValid (nV s) (kK s) = true := hv.mp (beq_iff_eq.mp hz)
    unfold valid
    refine WP.seq (WP.mono (numbers_ok e2) fun s3 ns => ?_)
    refine WP.ite (s3.gpr .r0 == 0) (eval_zero s3 .r0) (fun hz3 => ?_) (fun hz3 => ?_)
    · have hgo : s3.gpr .r0 = 0 := by simpa using hz3
      obtain ⟨odd, two⟩ := ns.go.mp hgo
      refine WP.mono (rest_ok ns hgo hmv) fun t ⟨ft, r3, bp, bq, res⟩ => ⟨ft, post_of ?_ r3 bp bq⟩
      have h1 : ¬(dV s * eV s < 2 ∨ (dV s * eV s - 1) % 2 = 1) := by omega
      rw [pk_eq, ite_eq_left hmv, VG.Proof.Rsa.recoverPrimes_go h1, ← mV_eq odd]
      change (match gos s recoverTries with
        | (some (p, q), tries) => (some (Spec.Rsa.i2osp p (kK s), Spec.Rsa.i2osp q (kK s)), tries)
        | (none, tries) => (none, tries)).1 = _
      generalize gos s recoverTries = G at res ⊢
      obtain ⟨g1, g2⟩ := G
      simp only at res
      subst res
      cases okB s <;> rfl
    · have hng : ¬ s3.gpr .r0 = 0 := fun e => by rw [e] at hz3; exact absurd hz3 (by decide)
      have h1 : dV s * eV s < 2 ∨ (dV s * eV s - 1) % 2 = 1 := by
        by_contra hc; exact hng (ns.go.mpr (by omega))
      refine WP.mono (fail_ok (ns.base.fin ns.ws.r30) ns.r21 ns.r23 ns.r25) fun t ⟨ft, t3, vp, vq, _⟩ =>
        ⟨ft, post_none ?_ t3 vp vq⟩
      rw [pk_eq, ite_eq_left hmv, VG.Proof.Rsa.recoverPrimes_none h1]
  · have hmv : ¬ Spec.Rsa.modulusValid (nV s) (kK s) = true := fun h' => by
      rw [hv.mpr h'] at hz; exact absurd hz (by decide)
    refine WP.mono (fail_ok (b2.fin e2.r30) a2.r21 a2.r23 a2.r25) fun t ⟨ft, t3, vp, vq, _⟩ =>
      ⟨ft, post_none ?_ t3 vp vq⟩
    rw [pk_eq, ite_eq_right hmv]

theorem rv_correct (s : State) (h : rvP.pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ rvP.post s t := by
  show WP isa code s fun t => abiPreserved s t ∧ rvP.post s t
  have hw := WP.keep rvRegs (c := code) (s := s) (Q := fun t => t.sp = s.sp ∧ t.lr = s.lr ∧
    (∀ r ∈ preserved, r ≠ .r2 → t.gpr r = s.gpr r) ∧ rvP.post s t) ?_ (by decide +kernel) (by decide +kernel)
  · refine WP.mono hw fun t ⟨⟨tsp, tlr, hr, post⟩, kt⟩ => ⟨⟨fun r hr' => ?_, tsp, tlr⟩, post⟩
    by_cases e : r = .r2
    · subst e; exact kt.gpr (r := .r2) (by decide)
    · exact hr r hr' e
  unfold code
  refine WP.seq (WP.mono (entry_ok h) fun s1 e1 => ?_)
  refine WP.seq (WP.mono (nCheck_ok e1.base e1.args) fun s2 ⟨⟨b2, a2, hv⟩, m2, k2⟩ => ?_)
  have e2 : REnt s s2 := ⟨b2, a2, (k2.gpr _ (by decide)).trans e1.r29, (k2.gpr _ (by decide)).trans e1.r30,
    m2.trans e1.mem, (e1.keep.trans k2).mono⟩
  rw [show Spec.Rsa.os2ip (nB0 s) = nV s from rfl] at hv
  refine WP.seq (WP.mono (branch_ok b2 a2 e2 hv) fun t ⟨ft, post⟩ => ?_)
  refine WP.mono (restore_ok ft) fun u ⟨⟨⟨u14, u15, u16, u17, u18, u19, u20, u21, u22, u23, u24, u25, u26, u27,
    u28, u29, u30, u31⟩, um⟩, ku⟩ => ⟨ku.sp.trans ft.sp, ku.lr.trans ft.lr, fun r hr hr2 => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> first | exact absurd rfl hr2 | with_reducible assumption
  · have e3 : u.gpr .r3 = t.gpr .r3 := ku.gpr _ (by decide)
    show Spec.Rsa.writtenAll u.mem _ _ _
    rw [um, e3]
    exact post

end VG.Proof.Rsa.PPC64LE.Recover
