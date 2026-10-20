module
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublic
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRunning

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingleCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSampleCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignAttempt
import VerifiedGarbage.Proof.Dsa.RandomSignTrace
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSample
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublic
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRunning
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingleCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSampleCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignAttempt
meta import VerifiedGarbage.Proof.Dsa.RandomSignTrace
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSample
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! A complete signing attempt leaks only its specified sampling and signing markers. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

private theorem cmp_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.subImm .x .x4 .x0 1]) (fun _ _ => True) := by
  exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) []
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun _ _ h => ⟨(), trivial, trivial, h⟩) (fun _ _ _ => trivial)

private theorem some_of_status {draw : Spec.Dsa.Random.Sample}
    (h : (BitVec.ofNat 64 (Random.sampleStatus draw) == 1) = true) : ∃ k, draw.scalar = some k := by
  cases hc : draw.scalar with
  | some k => exact ⟨k, rfl⟩
  | none =>
    simp only [Random.sampleStatus, hc] at h
    split at h <;> contradiction

theorem random_sign_attempt_agreement (v : Backend) {s t a b : State}
    {hs : RandomSignABI v.stack s} {ht : RandomSignABI v.stack t}
    {hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t)}
    {used fuel : Nat} (ha : RandomSignRunning hs hqs used (fuel + 1) a)
    (hb : RandomSignRunning ht hqt used (fuel + 1) b)
    (hpub : RandomSignPublicAgree s t) (hbound : fuel + 1 < 2 ^ 64)
    (htrace : (randomSignRemaining (randomInput s) used (fuel + 1)).trace =
      (randomSignRemaining (randomInput t) used (fuel + 1)).trace)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (RandomSign.attempt (randomSignerName v) (SignVerify.sign v.mul)) a tsa u)
    (eb : Exec isa (RandomSign.attempt (randomSignerName v) (SignVerify.sign v.mul)) b tsb w) : tsa = tsb := by
  have hdraw := congrArg randomSamplingTrace htrace
  rw [random_sign_trace_draw, random_sign_trace_draw] at hdraw
  obtain ⟨hused, _, hstatus⟩ := random_sign_draw_agree hpub hdraw
  cases ea with
  | seq eas ear => cases ear with
    | seq eac eai =>
      cases eb with
      | seq ebs ebr => cases ebr with
        | seq ebc ebi =>
          have hsample := random_sign_sample_agreement ha hb hpub hdraw eas ebs
          obtain ⟨haa, _, har, hna⟩ := random_post_of_exec (random_sign_sample ha) eas
          obtain ⟨hba, _, hbr, hnb⟩ := random_post_of_exec (random_sign_sample hb) ebs
          obtain ⟨⟨ham, haz⟩, hka⟩ := random_post_of_exec
            random_sign_test_one eac
          obtain ⟨⟨hbm, hbz⟩, hkb⟩ := random_post_of_exec
            random_sign_test_one ebc
          obtain ⟨_, _, hra⟩ := har.ready
          obtain ⟨_, _, hrb⟩ := hbr.ready
          have hcmp := (cmp_ct _ _ _ _ _ _ (hra.sp.trans (hpub.base.trans hrb.sp.symm)) eac ebc).1
          have har' := har.congr ham hka
          have hbr' := hbr.congr hbm hkb
          rw [haa] at haz
          rw [hba] at hbz
          cases eai with
          | iteT hca eata =>
            cases ebi with
            | iteT hcb ebtb =>
              change some ((_ : State).gpr .x4 == 0#64) = some _ at hca
              rw [haz] at hca
              simp only [Option.some.injEq] at hca
              change some ((_ : State).gpr .x4 == 0#64) = some _ at hcb
              rw [hbz] at hcb
              simp only [Option.some.injEq] at hcb
              obtain ⟨k, hk⟩ := some_of_status hca
              obtain ⟨l, hl⟩ := some_of_status hcb
              have hsucc := random_sign_trace_call htrace hk hl
              have hnoncea := hna k hk
              have hnonceb := hnb l hl
              rw [← ham] at hnoncea
              rw [← hbm] at hnonceb
              rw [← hused] at hbr'
              have hsingle := random_sign_single_agreement v har' hbr' hpub (by omega) hbound
                hnoncea hnonceb hsucc eata ebtb
              rw [hsample, hcmp, hsingle]
            | iteF hcb _ =>
              change some ((_ : State).gpr .x4 == 0#64) = some _ at hca
              rw [haz] at hca
              simp only [Option.some.injEq, hstatus] at hca
              change some ((_ : State).gpr .x4 == 0#64) = some _ at hcb
              rw [hbz] at hcb
              simp only [Option.some.injEq] at hcb
              rw [hca] at hcb
              contradiction
          | iteF hca eata =>
            cases ebi with
            | iteT hcb _ =>
              change some ((_ : State).gpr .x4 == 0#64) = some _ at hca
              rw [haz] at hca
              simp only [Option.some.injEq, hstatus] at hca
              change some ((_ : State).gpr .x4 == 0#64) = some _ at hcb
              rw [hbz] at hcb
              simp only [Option.some.injEq] at hcb
              rw [hca] at hcb
              contradiction
            | iteF _ ebtb =>
              have hnil := (RelCT.block_nil (P := fun _ _ => True) (fun _ _ _ => True.intro)
                _ _ _ _ _ _ trivial eata ebtb).1
              rw [hsample, hcmp, hnil]

end VG.Proof.Dsa.AArch64
