module
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublic

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignBodyCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinishAgreement
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingleCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInvalid
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublic
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignBodyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinishAgreement
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingleCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInvalid
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Rejection before sampling has a fixed schedule for the same public arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

private theorem invalid_store_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block (Random.store Random.oStatus .x0)) (fun _ _ => True) := by
  exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) []
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun _ _ h => ⟨(), trivial, trivial, h⟩) (fun _ _ _ => trivial)

private theorem invalid_tail (v : Backend) {s t a b : State}
    (hs : RandomSignABI v.stack s) (ht : RandomSignABI v.stack t)
    (ha : RandomSignFinishPre s 0 a) (hb : RandomSignFinishPre t 0 b)
    (hra : a.gpr .x0 = 0) (hrb : b.gpr .x0 = 0) (hp : RandomSignPublicAgree s t)
    {tsa tsb : List Leak} {u w : State} (ea : Exec isa (randomSignTail v) a tsa u)
    (eb : Exec isa (randomSignTail v) b tsb w) : tsa = tsb := by
  cases ea with
  | seq eai eaf =>
    cases eb with
    | seq ebi ebf =>
      cases eai with
      | iteF hc _ => simp [eval, State.read, hra] at hc
      | iteT _ east =>
        cases ebi with
        | iteF hc _ => simp [eval, State.read, hrb] at hc
        | iteT _ ebst =>
          have hstore := (invalid_store_ct _ _ _ _ _ _
            (ha.sp.trans (hp.base.trans hb.sp.symm)) east ebst).1
          obtain ⟨hfa, hsa⟩ := random_post_of_exec (random_sign_invalid_store ha hra) east
          obtain ⟨hfb, hsb⟩ := random_post_of_exec (random_sign_invalid_store hb hrb) ebst
          have hfinish := random_finish_agreement hs ht hfa hfb hp hsa hsb eaf ebf
          rw [hstore, hfinish]

theorem random_sign_body_invalid_ct (v : Backend) {s t : State}
    (hs : RandomSignABI v.stack s) (ht : RandomSignABI v.stack t) (hp : RandomSignPublicAgree s t)
    (hq : ¬ 1 < Spec.Dsa.decodeBE (randomQBytes s))
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.mul)) (allocated Random.frameBytes s) tsa u)
    (eb : Exec isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.mul)) (allocated Random.frameBytes t) tsb w) : tsa = tsb := by
  have hqt : ¬ 1 < Spec.Dsa.decodeBE (randomQBytes t) := by rw [← hp.qbytes]; exact hq
  cases ea with
  | seq eae ear => cases ear with
    | seq eap eat =>
      cases eb with
      | seq ebe ebr => cases ebr with
        | seq ebp ebt =>
          have hinit := random_sign_init_agreement hs ht hp (.seq eae eap) (.seq ebe ebp)
          obtain ⟨hra, har⟩ := random_post_of_exec (random_sign_init_invalid hs hq) (.seq eae eap)
          obtain ⟨hrb, hbr⟩ := random_post_of_exec (random_sign_init_invalid ht hqt) (.seq ebe ebp)
          have htail := invalid_tail v hs ht har hbr hra hrb hp eat ebt
          rw [← List.append_assoc, ← List.append_assoc, hinit, htail]

end VG.Proof.Dsa.AArch64
