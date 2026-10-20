module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignLoopCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInitCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinishAgreement
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignLoopCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInitCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinishAgreement
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingleCT

/-! Compose initialization, retries, and publication for valid subgroup moduli. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_sign_init_agreement {extra : Nat} {s t : State}
    (hs : RandomSignABI extra s) (ht : RandomSignABI extra t) (hp : RandomSignPublicAgree s t)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (.seq (.block RandomSign.entry) Random.prepare) (allocated Random.frameBytes s) tsa u)
    (eb : Exec isa (.seq (.block RandomSign.entry) Random.prepare) (allocated Random.frameBytes t) tsb w) : tsa = tsb := by
  have he : (⟨randomBase s, s.gpr .x3 + s.gpr .x5, randomQBytes s⟩ : RandomPreparePublic) =
      ⟨randomBase t, t.gpr .x3 + t.gpr .x5, randomQBytes t⟩ := by
    rw [hp.base, hp.regs .x3 (by decide), hp.regs .x5 (by decide), hp.qbytes]
  exact (random_sign_init_ct _ _ _ _ _ _
    ⟨_, ⟨s, extra, hs, rfl, rfl⟩, ⟨t, extra, ht, rfl, he⟩, hp.base⟩ ea eb).1

def randomSignTail (v : Backend) : Prog isa :=
  .seq (.ite (.zero .x .x0) (.block (Random.store Random.oStatus .x0))
    (.loop (.seq (RandomSign.attempt (randomSignerName v) (SignVerify.sign v.mul)) randomSignStatusTest)
      (.zero .x .x4))) RandomSign.finish

private theorem valid_tail (v : Backend) {s t a b : State}
    {hs : RandomSignABI v.stack s} {ht : RandomSignABI v.stack t}
    {hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t)}
    (ha : RandomSignRunning hs hqs 0 8 a) (hb : RandomSignRunning ht hqt 0 8 b)
    (hra : a.gpr .x0 = 1) (hrb : b.gpr .x0 = 1) (hp : RandomSignPublicAgree s t)
    (htrace : (randomSignRemaining (randomInput s) 0 8).trace = (randomSignRemaining (randomInput t) 0 8).trace)
    (hstatus : (randomSignRemaining (randomInput s) 0 8).status = (randomSignRemaining (randomInput t) 0 8).status)
    {tsa tsb : List Leak} {u w : State} (ea : Exec isa (randomSignTail v) a tsa u)
    (eb : Exec isa (randomSignTail v) b tsb w) : tsa = tsb := by
  cases ea with
  | seq eai eaf =>
    cases eb with
    | seq ebi ebf =>
      cases eai with
      | iteT hc _ => simp [eval, State.read, hra] at hc
      | iteF _ eal =>
        cases ebi with
        | iteT hc _ => simp [eval, State.read, hrb] at hc
        | iteF _ ebl =>
          have hloop := (random_sign_loop_ct v hp 8 _ _ _ _ _ _
            ⟨by decide, by decide, 0, ha, hb, htrace⟩ eal ebl).1
          obtain ⟨⟨_, hrunA⟩, hsta, _⟩ := random_post_of_exec (random_sign_loop_correct v ha (by decide) (by decide)) eal
          obtain ⟨⟨_, hrunB⟩, hstb, _⟩ := random_post_of_exec (random_sign_loop_correct v hb (by decide) (by decide)) ebl
          rw [← hstatus] at hstb
          have hfinish := random_finish_agreement hs ht hrunA.finishPre hrunB.finishPre hp hsta hstb eaf ebf
          rw [hloop, hfinish]

theorem random_sign_body_valid_ct (v : Backend) {s t : State}
    (hs : RandomSignABI v.stack s) (ht : RandomSignABI v.stack t) (hp : RandomSignPublicAgree s t)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s))
    (htrace : (randomSignRemaining (randomInput s) 0 8).trace = (randomSignRemaining (randomInput t) 0 8).trace)
    (hstatus : (randomSignRemaining (randomInput s) 0 8).status = (randomSignRemaining (randomInput t) 0 8).status)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.mul)) (allocated Random.frameBytes s) tsa u)
    (eb : Exec isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.mul)) (allocated Random.frameBytes t) tsb w) : tsa = tsb := by
  have hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t) := by rw [← hp.qbytes]; exact hq
  cases ea with
  | seq eae ear => cases ear with
    | seq eap eat =>
      cases eb with
      | seq ebe ebr => cases ebr with
        | seq ebp ebt =>
          have hinit := random_sign_init_agreement hs ht hp (.seq eae eap) (.seq ebe ebp)
          obtain ⟨hra, har⟩ := random_post_of_exec (random_sign_init_running hs hq) (.seq eae eap)
          obtain ⟨hrb, hbr⟩ := random_post_of_exec (random_sign_init_running ht hqt) (.seq ebe ebp)
          have htail := valid_tail v har hbr hra hrb hp htrace hstatus eat ebt
          rw [← List.append_assoc, ← List.append_assoc, hinit, htail]

end VG.Proof.Dsa.AArch64
