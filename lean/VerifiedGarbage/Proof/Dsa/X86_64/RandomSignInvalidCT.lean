module
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignPublic

import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignBodyCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinishAgreement
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingleCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInvalid
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignBody
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignPublic
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignBodyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinishAgreement
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingleCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInvalid
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignBody
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Rejection before sampling has a fixed schedule for the same public arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

private theorem invalid_store_ct : RelCT isa (fun s t => s.gpr .rsp = t.gpr .rsp)
    (.block [.store (Random.sp Random.oStatus) .rax]) (fun _ _ => True) := by
  refine (two_taint (Φ := fun (B : Addr) s => s.gpr .rsp = B) [.rsp] ?_ (by taint_decide)).mono
    (fun s _ h => ⟨s.gpr .rsp, rfl, h.symm⟩) (fun _ _ _ => trivial)
  intro B s t hs ht r hr
  rw [List.mem_singleton] at hr
  subst r
  exact hs.trans ht.symm

private theorem invalid_tail (v : Backend) {s t a b : State}
    (hs : RandomSignABI v.stack s) (ht : RandomSignABI v.stack t)
    (ha : RandomSignFinishPre s 0 a) (hb : RandomSignFinishPre t 0 b)
    (hra : a.gpr .rax = 0) (hrb : b.gpr .rax = 0) (hp : RandomSignPublicAgree s t)
    {tsa tsb : List Leak} {u w : State} (ea : Exec isa (randomSignTail v) a tsa u)
    (eb : Exec isa (randomSignTail v) b tsb w) : tsa = tsb := by
  cases ea with
  | seq eac ear => cases ear with
    | seq eai eaf =>
      cases eb with
      | seq ebc ebr => cases ebr with
        | seq ebi ebf =>
          have hcmp := (random_sign_cmp_zero_ct _ _ _ _ _ _ trivial eac ebc).1
          obtain ⟨haz, haw⟩ := random_post_of_exec (random_sign_invalid_store ha hra) eac
          obtain ⟨hbz, hbw⟩ := random_post_of_exec (random_sign_invalid_store hb hrb) ebc
          obtain ⟨_, hka⟩ := random_post_of_exec random_sign_test_zero eac
          obtain ⟨_, hkb⟩ := random_post_of_exec random_sign_test_zero ebc
          cases eai with
          | iteF hc _ => simp only [eval, haz] at hc; contradiction
          | iteT _ east =>
            cases ebi with
            | iteF hc _ => simp only [eval, hbz] at hc; contradiction
            | iteT _ ebst =>
              have hstore := (invalid_store_ct _ _ _ _ _ _
                (((hka.gpr (by decide)).trans ha.sp).trans
                  (hp.base.trans ((hkb.gpr (by decide)).trans hb.sp).symm)) east ebst).1
              obtain ⟨hfa, hsa⟩ := random_post_of_exec haw east
              obtain ⟨hfb, hsb⟩ := random_post_of_exec hbw ebst
              have hfinish := random_finish_agreement hs ht hfa hfb hp hsa hsb eaf ebf
              rw [hcmp, hstore, hfinish]

theorem random_sign_body_invalid_ct (v : Backend) {s t : State}
    (hs : RandomSignABI v.stack s) (ht : RandomSignABI v.stack t) (hp : RandomSignPublicAgree s t)
    (hq : ¬ 1 < Spec.Dsa.decodeBE (randomQBytes s))
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.sq v.mul)) (allocState Random.frameBytes s) tsa u)
    (eb : Exec isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.sq v.mul)) (allocState Random.frameBytes t) tsb w) : tsa = tsb := by
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

end VG.Proof.Dsa.X86_64
