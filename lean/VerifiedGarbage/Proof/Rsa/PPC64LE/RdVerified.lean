module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdCT1
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdCorrect
public import VerifiedGarbage.Impl.Rsa.PPC64LE.RecoverDet
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RdCT1
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RdCorrect
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdFinish
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.RdFinish

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: constant time, and verified

`rd_ct`: after the entry and the check of `n` (`RdCT1.lean`):
for a valid modulus the loads, `d e`, Appendix C.2 and the stores
(`RecoverDet.valid`) are checked by `taint_decide` on the registers that
hold the pointers, the lengths and `w` (every count is set from `w`, every
choice a masked selection), and whether `n` is valid is public.
`rd_verified`: against the shared contract.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RecDet

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Impl.Rsa.PPC64LE.RecoverDet (code valid)
open VG.Impl.Rsa.PPC64LE.Recover (fail restore)
open VG.Impl.Rsa.PPC64LE.RecoverDet (det deMinus twos gcd aProduct divA divB square minus4n sqrt factors sB0 sB1)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)

/-- Before the restore. -/
def DD (d : RdD) (u : State) : Prop := ∃ s0, D0 d s0 ∧ RFin s0 u

theorem pins_D4 : Pins D4 [.r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31] := by
  rintro d s₁ s₂ ⟨a, ha, e₁, -⟩ ⟨b, hb, e₂, -⟩ r hr
  exact pins_D2 d s₁ s₂ ⟨a, ha, e₁⟩ ⟨b, hb, e₂⟩ r hr

theorem pins_DD : Pins DD [.r30, .r31] := by
  rintro d s₁ s₂ ⟨a, ha, f₁⟩ ⟨b, hb, f₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [f₁.r30, f₂.r30, ha.k hb]
  · rw [f₁.r31, f₂.r31]; exact ha.arg hb (by decide)

theorem DD_valid [VG.Proof.Rsa.PPC64LE.InvLaw] {d : RdD} {s : State}
    (h : D4 d s ∧ isa.eval (.zero .d .r0) s = some true) : WP isa valid s (DD d) := by
  obtain ⟨⟨s0, hs, e, hv⟩, hc⟩ := h
  rw [eval_zero] at hc
  have hmv := hv.mp (beq_iff_eq.mp (Option.some.inj hc))
  exact WP.mono (valid_ok hs.1 e hmv) fun u ⟨fu, _⟩ => ⟨s0, hs, fu⟩

theorem DD_fail {d : RdD} {s : State} (h : D4 d s ∧ isa.eval (.zero .d .r0) s = some false) :
    WP isa fail s (DD d) := by
  obtain ⟨⟨s0, hs, e, -⟩, -⟩ := h
  exact WP.mono (fail_ok (e.base.fin e.r30) e.args.r21 e.args.r23 e.args.r25) fun u ⟨fu, _⟩ => ⟨s0, hs, fu⟩

/-- The valid branch up to the GCD, which calls the inverse. -/
abbrev preG : Prog isa := seqs [VG.Impl.Rsa.PPC64LE.Recover.loads, VG.Impl.Rsa.PPC64LE.Recover.prod, deMinus, twos, gcd]

/-- And the rest. -/
abbrev restG : Prog isa :=
  seqs [aProduct, divA, divB, square, minus4n, sqrt, factors, VG.Impl.Rsa.PPC64LE.Recover.stores]

theorem flat_valid : valid.flat = preG.flat ++ restG.flat := by
  simp only [valid, det, preG, restG, seqs, Code.flat, List.append_assoc]

/-- After the GCD: the state the rest of the valid branch starts from, whose
pointers the inverse reloads from memory, and the rest then reaches `DD`. -/
def G (d : RdD) (u : State) : Prop :=
  (∃ s0 A V, D0 d s0 ∧ DS s0 false A [(true, 8), (true, 12), (true, 15), (true, 9), (false, 32)] V [sB1, sB0] u) ∧
    WP isa restG u (DD d)

theorem pins_G : Pins G [.r21, .r23, .r25, .r29, .r30, .r31] := by
  rintro d s₁ s₂ ⟨⟨a, A₁, V₁, ha, e₁⟩, -⟩ ⟨⟨b, A₂, V₂, hb, e₂⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e₁.r21, e₂.r21]; exact ha.reg hb (by decide)
  · rw [e₁.r23, e₂.r23]; exact ha.reg hb (by decide)
  · rw [e₁.r25, e₂.r25]; exact ha.reg hb (by decide)
  · rw [e₁.ws.r29, e₂.ws.r29, vw, vw, ha.k hb]
  · rw [e₁.ws.r30, e₂.ws.r30, vw, vw, ha.k hb]
  · rw [e₁.base.r31, e₂.base.r31]; exact ha.arg hb (by decide)

theorem pre_G [VG.Proof.Rsa.PPC64LE.InvLaw] {d : RdD} {s : State}
    (h : D4 d s ∧ isa.eval (.zero .d .r0) s = some true) : WP isa preG s (G d) := by
  obtain ⟨⟨s0, hs, e, hv⟩, hc⟩ := id h
  rw [eval_zero] at hc
  have hmv := hv.mp (beq_iff_eq.mp (Option.some.inj hc))
  exact WP.and (WP.mono (valid_gcd_ok e hmv) fun _ ⟨A, V, h3⟩ => ⟨s0, A, V, hs, h3⟩)
    (Keys.WP.cut flat_valid (DD_valid h))

/-- The valid branch, in two: the pointers pinned again after the GCD. -/
theorem validG_ct [VG.Proof.Rsa.PPC64LE.InvLaw] :
    RelCT isa (Two fun d s => D4 d s ∧ isa.eval (.zero .d .r0) s = some true) valid (Two DD) :=
  Keys.RelCT.cut flat_valid
    (two_post (two_taint _ (fun d s₁ s₂ h₁ h₂ => pins_D4 d s₁ s₂ h₁.1 h₂.1) (by taint_decide)) fun _ _ h => pre_G h)
    (two_post (two_taint _ pins_G (by taint_decide)) fun _ _ h => h.2)

theorem validD_eq {d : RdD} {s₁ s₂ : State} (h₁ : D4 d s₁) (h₂ : D4 d s₂) :
    isa.eval (.zero .d .r0) s₁ = isa.eval (.zero .d .r0) s₂ := by
  obtain ⟨a, ha, -, va⟩ := h₁
  obtain ⟨b, hb, -, vb⟩ := h₂
  rw [eval_zero, eval_zero]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, va, vb, ha.nV hb, ha.k hb]

theorem branchD_ct [VG.Proof.Rsa.PPC64LE.InvLaw] :
    RelCT isa (Two D4) (.ite (.zero .d .r0) valid fail) (Two DD) := by
  refine RelCT.ite (fun s₁ s₂ ⟨d, h₁, h₂, _⟩ => validD_eq h₁ h₂) ?_ ?_
  · exact validG_ct.mono
      (fun s₁ s₂ ⟨⟨d, h₁, h₂, sp⟩, hc⟩ => ⟨d, ⟨h₁, hc⟩, ⟨h₂, (validD_eq h₁ h₂) ▸ hc⟩, sp⟩) fun _ _ h => h
  · exact (two_post (Φ := fun d s => D4 d s ∧ isa.eval (.zero .d .r0) s = some false)
      (two_taint _ (fun d s₁ s₂ h₁ h₂ => pins_D4 d s₁ s₂ h₁.1 h₂.1) (by taint_decide)) fun _ _ h => DD_fail h).mono
      (fun s₁ s₂ ⟨⟨d, h₁, h₂, sp⟩, hc⟩ => ⟨d, ⟨h₁, hc⟩, ⟨h₂, (validD_eq h₁ h₂) ▸ hc⟩, sp⟩) fun _ _ h => h

theorem rd_rel [VG.Proof.Rsa.PPC64LE.InvLaw] : RelCT isa (Two D0) code fun _ _ => True := by
  unfold code
  exact RelCT.seq rd_entry_ct (RelCT.seq rd_check_ct (RelCT.seq branchD_ct (two_taint _ pins_DD (by taint_decide))))

theorem rd_ct [VG.Proof.Rsa.PPC64LE.InvLaw] : ConstantTime isa rdP.pre rdP.pub code :=
  RelCT.constantTime (rd_rel.mono (fun s t ⟨hs, ht, hr, hsp, hst, hb⟩ => by
    refine ⟨rdPub s, ⟨hs, rfl⟩, ⟨ht, ?_⟩, hsp⟩
    simp only [rdPub, RdD.mk.injEq]
    exact ⟨(List.map_inj_left.mpr hr).symm, hst.symm, hb.symm⟩) fun _ _ h => h)


/-- `vg_rsa_recover_primes_det`. -/
theorem rd_verified [VG.Proof.Rsa.PPC64LE.InvLaw] :
    Verified target VG.Impl.Rsa.PPC64LE.RecoverDet.code (Spec.Rsa.recoverPrimesDetContract abi) :=
  Verified.of_correct rd_correct rd_ct VG.Proof.Rsa.PPC64LE.Recover.rd_implies

end VG.Proof.Rsa.PPC64LE.RecDet
