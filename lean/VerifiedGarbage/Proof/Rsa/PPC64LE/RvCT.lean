module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCT2
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCT2
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Rsa.RecoverTries
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCF
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFF
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFail
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFin
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvMont
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvRest
import VerifiedGarbage.Proof.Rsa.RecoverExp
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCF
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCand
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCandSet
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFail
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFin
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvMont
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvNumbers
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RvRest
meta import VerifiedGarbage.Proof.Rsa.RecoverMath
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCand
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCandSet
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvNumbers

/-!
# `vg_rsa_recover_primes` on PPC64LE: constant time

`rv_ct`: as `CvCT.lean`, with the cuts of `RvCT1.lean` and `RvCT2.lean`, and
after `numbers` whether `d e - 1` is even and positive, which the skip tests:
it is whether `recoverPrimes` tries a candidate at all, so public.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Spec.Rsa (recoverPrimes recoverTries primesKey splitTwos)
open VG.Impl.Rsa.PPC64LE.Recover (code valid numbers rest fail mont candLoop fin restore)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)

/-- For a valid `n`, whether a candidate is tried at all. -/
theorem skip_iff {s0 : State} (hmv : Spec.Rsa.modulusValid (nV s0) (kK s0) = true) :
    (dV s0 * eV s0 % 2 = 1 ∧ 2 ≤ dV s0 * eV s0) ↔ (primesKey (nB s0) (eB s0) (dB s0)).2 ≠ 0 := by
  rw [tries_eq, ite_eq_left hmv]
  by_cases h : dV s0 * eV s0 < 2 ∨ (dV s0 * eV s0 - 1) % 2 = 1
  · rw [VG.Proof.Rsa.recoverPrimes_none h]; simp only [ne_eq, not_true_eq_false, iff_false]; omega
  · rw [VG.Proof.Rsa.recoverPrimes_go h]
    have := VG.Proof.Rsa.go_pos (nV s0) (splitTwos (dV s0 * eV s0 - 1)).1 (splitTwos (dV s0 * eV s0 - 1)).2
      recoverTries (Nat.le_refl _)
    constructor
    · intro _; omega
    · intro _; omega

/-- After the numbers. -/
def R5 (d : RvD) (u : State) : Prop :=
  ∃ s0, R0 d s0 ∧ Spec.Rsa.modulusValid (nV s0) (kK s0) = true ∧ NumS s0 u

/-- Before the restore. -/
def RD (d : RvD) (u : State) : Prop := ∃ s0, R0 d s0 ∧ RFin s0 u

theorem pins_R4 : Pins R4 [.r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31] := by
  rintro d s₁ s₂ ⟨a, ha, e₁, -⟩ ⟨b, hb, e₂, -⟩ r hr
  exact pins_R2 d s₁ s₂ ⟨a, ha, e₁⟩ ⟨b, hb, e₂⟩ r hr

theorem pins_R5 : Pins R5 [.r21, .r23, .r24, .r25, .r26, .r29, .r30, .r31] := by
  rintro d s₁ s₂ ⟨a, ha, -, n₁⟩ ⟨b, hb, -, n₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [n₁.r21, n₂.r21]; exact ha.reg hb (by decide)
  · rw [n₁.r23, n₂.r23]; exact ha.reg hb (by decide)
  · rw [n₁.r24, n₂.r24]; exact ha.reg hb (by decide)
  · rw [n₁.r25, n₂.r25]; exact ha.reg hb (by decide)
  · rw [n₁.r26, n₂.r26, ha.cB hb]
  · rw [n₁.ws.r29, n₂.ws.r29, ha.k hb]
  · rw [n₁.ws.r30, n₂.ws.r30, ha.k hb]
  · rw [n₁.ws.r31, n₂.ws.r31]; exact ha.arg hb (by decide)

theorem pins_CE : Pins CE [.r21, .r23, .r25, .r26, .r29, .r30, .r31] := by
  rintro d s₁ s₂ ⟨a, ha, -, ⟨c₁, -⟩, -⟩ ⟨b, hb, -, ⟨c₂, -⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [c₁.r21, c₂.r21]; exact ha.reg hb (by decide)
  · rw [c₁.r23, c₂.r23]; exact ha.reg hb (by decide)
  · rw [c₁.r25, c₂.r25]; exact ha.reg hb (by decide)
  · rw [c₁.r26, c₂.r26, ha.cB hb]
  · rw [c₁.ws.r29, c₂.ws.r29, ha.k hb]
  · rw [c₁.ws.r30, c₂.ws.r30, ha.k hb]
  · rw [c₁.ws.r31, c₂.ws.r31]; exact ha.arg hb (by decide)

theorem pins_RD : Pins RD [.r30, .r31] := by
  rintro d s₁ s₂ ⟨a, ha, f₁⟩ ⟨b, hb, f₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [f₁.r30, f₂.r30, ha.k hb]
  · rw [f₁.r31, f₂.r31]; exact ha.arg hb (by decide)

theorem R5_of {d : RvD} {s : State} (h : R4 d s ∧ isa.eval (.zero .d .r0) s = some true) : WP isa numbers s (R5 d) := by
  obtain ⟨⟨s0, hs, e, hv⟩, hc⟩ := h
  rw [eval_zero] at hc
  have hmv := hv.mp (beq_iff_eq.mp (Option.some.inj hc))
  exact WP.mono (numbers_ok e) fun u nu => ⟨s0, hs, hmv, nu⟩

theorem CL0_of {d : RvD} {s : State} (h : R5 d s ∧ isa.eval (.zero .d .r0) s = some true) :
    WP isa mont s (CL0 d) := by
  obtain ⟨⟨s0, hs, hmv, ns⟩, hc⟩ := h
  rw [eval_zero] at hc
  have hgo := beq_iff_eq.mp (Option.some.inj hc)
  obtain ⟨odd, two⟩ := ns.go.mp hgo
  exact WP.mono (mont_ok ns hgo hmv) fun u hu =>
    ⟨s0, hs, NOk.of_valid hmv, par_of ns.base.pre odd two, nt_eq hmv odd two, hu.cf⟩

theorem RD_fin {d : RvD} {s : State} (h : CE d s) : WP isa fin s (RD d) := by
  obtain ⟨s0, hs, hn, cp, -⟩ := h
  exact WP.mono (fin_ok hn cp) fun u ⟨fu, _⟩ => ⟨s0, hs, fu⟩

theorem RD_skip {d : RvD} {s : State} (h : R5 d s ∧ isa.eval (.zero .d .r0) s = some false) : WP isa fail s (RD d) := by
  obtain ⟨⟨s0, hs, -, ns⟩, -⟩ := h
  exact WP.mono (fail_ok (ns.base.fin ns.ws.r30) ns.r21 ns.r23 ns.r25) fun u ⟨fu, _⟩ => ⟨s0, hs, fu⟩

theorem RD_fail {d : RvD} {s : State} (h : R4 d s ∧ isa.eval (.zero .d .r0) s = some false) : WP isa fail s (RD d) := by
  obtain ⟨⟨s0, hs, e, -⟩, -⟩ := h
  exact WP.mono (fail_ok (e.base.fin e.r30) e.args.r21 e.args.r23 e.args.r25) fun u ⟨fu, _⟩ => ⟨s0, hs, fu⟩

theorem rest_ct : RelCT isa (Two fun d s => R5 d s ∧ isa.eval (.zero .d .r0) s = some true) rest (Two RD) := by
  unfold rest
  refine RelCT.seq (two_post (two_taint _ (fun d s₁ s₂ h₁ h₂ => pins_R5 d s₁ s₂ h₁.1 h₂.1) (by taint_decide))
    fun _ _ h => CL0_of h) (RelCT.seq cand_ct (two_post (two_taint _ pins_CE (by taint_decide)) fun _ _ h => RD_fin h))

theorem skip_eq {d : RvD} {s₁ s₂ : State} (h₁ : R5 d s₁) (h₂ : R5 d s₂) :
    isa.eval (.zero .d .r0) s₁ = isa.eval (.zero .d .r0) s₂ := by
  obtain ⟨a, ha, va, na⟩ := h₁
  obtain ⟨b, hb, vb, nb⟩ := h₂
  rw [eval_zero, eval_zero]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, na.go, nb.go, skip_iff va, skip_iff vb, ha.tries hb]

theorem valid_ct : RelCT isa (Two fun d s => R4 d s ∧ isa.eval (.zero .d .r0) s = some true) valid (Two RD) := by
  unfold valid
  refine RelCT.seq (two_post (two_taint _ (fun d s₁ s₂ h₁ h₂ => pins_R4 d s₁ s₂ h₁.1 h₂.1) (by taint_decide))
    fun _ _ h => R5_of h) (RelCT.ite (fun s₁ s₂ ⟨d, h₁, h₂, _⟩ => skip_eq h₁ h₂) ?_ ?_)
  · exact rest_ct.mono (fun s₁ s₂ ⟨⟨d, h₁, h₂, sp⟩, hc⟩ =>
      ⟨d, ⟨h₁, hc⟩, ⟨h₂, (skip_eq h₁ h₂) ▸ hc⟩, sp⟩) fun _ _ h => h
  · exact (two_post (Φ := fun d s => R5 d s ∧ isa.eval (.zero .d .r0) s = some false)
      (two_taint _ (fun d s₁ s₂ h₁ h₂ => pins_R5 d s₁ s₂ h₁.1 h₂.1) (by taint_decide)) fun _ _ h => RD_skip h).mono
      (fun s₁ s₂ ⟨⟨d, h₁, h₂, sp⟩, hc⟩ => ⟨d, ⟨h₁, hc⟩, ⟨h₂, (skip_eq h₁ h₂) ▸ hc⟩, sp⟩) fun _ _ h => h

theorem valid_eq {d : RvD} {s₁ s₂ : State} (h₁ : R4 d s₁) (h₂ : R4 d s₂) :
    isa.eval (.zero .d .r0) s₁ = isa.eval (.zero .d .r0) s₂ := by
  obtain ⟨a, ha, -, va⟩ := h₁
  obtain ⟨b, hb, -, vb⟩ := h₂
  rw [eval_zero, eval_zero]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, va, vb, ha.nV hb, ha.k hb]

theorem branch_ct : RelCT isa (Two R4) (.ite (.zero .d .r0) valid fail) (Two RD) := by
  refine RelCT.ite (fun s₁ s₂ ⟨d, h₁, h₂, _⟩ => valid_eq h₁ h₂) ?_ ?_
  · exact valid_ct.mono (fun s₁ s₂ ⟨⟨d, h₁, h₂, sp⟩, hc⟩ =>
      ⟨d, ⟨h₁, hc⟩, ⟨h₂, (valid_eq h₁ h₂) ▸ hc⟩, sp⟩) fun _ _ h => h
  · exact (two_post (Φ := fun d s => R4 d s ∧ isa.eval (.zero .d .r0) s = some false)
      (two_taint _ (fun d s₁ s₂ h₁ h₂ => pins_R4 d s₁ s₂ h₁.1 h₂.1) (by taint_decide)) fun _ _ h => RD_fail h).mono
      (fun s₁ s₂ ⟨⟨d, h₁, h₂, sp⟩, hc⟩ => ⟨d, ⟨h₁, hc⟩, ⟨h₂, (valid_eq h₁ h₂) ▸ hc⟩, sp⟩) fun _ _ h => h

theorem rv_rel : RelCT isa (Two R0) code fun _ _ => True := by
  unfold code
  exact RelCT.seq rv_entry_ct (RelCT.seq rv_check_ct (RelCT.seq branch_ct (two_taint _ pins_RD (by taint_decide))))

theorem rv_ct : ConstantTime isa rvP.pre rvP.pub code :=
  RelCT.constantTime (rv_rel.mono (fun s t ⟨hs, ht, hr, hsp, hst, hb⟩ => by
    obtain ⟨hne, htr⟩ := List.append_inj' hb (List.length_singleton.trans List.length_singleton.symm)
    refine ⟨rvPub s, ⟨hs, rfl⟩, ⟨ht, ?_⟩, hsp⟩
    simp only [rvPub, RvD.mk.injEq]
    exact ⟨(List.map_inj_left.mpr hr).symm, hst.symm, hne.symm, (List.singleton_inj.mp htr).symm⟩) fun _ _ h => h)

end VG.Proof.Rsa.PPC64LE.Recover
