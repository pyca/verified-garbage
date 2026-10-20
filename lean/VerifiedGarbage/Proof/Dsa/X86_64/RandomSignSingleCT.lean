module
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignPublic
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingle

import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallObserve
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignPublic
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingle
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallObserve
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! One complete signing call leaks its public key and success bit only. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_post_of_exec {c : Prog isa} {s t : State} {trace : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (he : Exec isa c s trace t) : Q t := by
  obtain ⟨_, u, hu, hq⟩ := h
  obtain ⟨_, heq⟩ := Exec.det he hu
  rw [heq]
  exact hq

theorem random_callArgs_ct : RelCT isa (fun s t => s.gpr .rsp = t.gpr .rsp)
    (.block RandomSign.callArgs) (fun _ _ => True) := by
  refine (two_taint (Φ := fun (B : Addr) s => s.gpr .rsp = B) [.rsp] ?_ (by taint_decide)).mono
    (fun s _ h => ⟨s.gpr .rsp, rfl, h.symm⟩) (fun _ _ _ => trivial)
  intro B s t hs ht r hr
  rw [List.mem_singleton] at hr
  subst r
  exact hs.trans ht.symm

theorem random_sign_single_agreement (v : Backend) {s t a b : State}
    {hs : RandomSignABI v.stack s} {ht : RandomSignABI v.stack t}
    {hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t)}
    {used fuel k l : Nat} (ha : RandomSignRunning hs hqs used fuel a) (hb : RandomSignRunning ht hqt used fuel b)
    (hpub : RandomSignPublicAgree s t) (hf : 0 < fuel) (hbound : fuel < 2 ^ 64)
    (hna : Spec.Rsa.bytesAt a.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat = Spec.Dsa.encodeBE (stackArg s 0).toNat k)
    (hnb : Spec.Rsa.bytesAt b.mem (off (randomBase t) Random.oNonce) (stackArg t 0).toNat = Spec.Dsa.encodeBE (stackArg t 0).toNat l)
    (hsuccess : (randomSingleResult s k).isSome = (randomSingleResult t l).isSome)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (.seq (.block RandomSign.callArgs)
      (.seq (.call (randomSignerName v) (SignVerify.sign v.sq v.mul)) RandomSign.callFinish)) a tsa u)
    (eb : Exec isa (.seq (.block RandomSign.callArgs)
      (.seq (.call (randomSignerName v) (SignVerify.sign v.sq v.mul)) RandomSign.callFinish)) b tsb w) : tsa = tsb := by
  cases ea with
  | seq eaa ear => cases ear with
    | seq eac eaf =>
      cases eb with
      | seq eba ebr => cases ebr with
        | seq ebc ebf =>
          obtain ⟨_, _, hra⟩ := ha.ready
          obtain ⟨_, _, hrb⟩ := hb.ready
          have hargs := (random_callArgs_ct _ _ _ _ _ _
            (hra.sp.trans (hpub.base.trans hrb.sp.symm)) eaa eba).1
          obtain ⟨hca, hresa, hkeya, hfua⟩ := random_post_of_exec (random_callArgs_observe v ha hna) eaa
          obtain ⟨hcb, hresb, hkeyb, hfub⟩ := random_post_of_exec (random_callArgs_observe v hb hnb) eba
          have hstatus : Spec.Dsa.signStatus (randomSingleResult s k) = Spec.Dsa.signStatus (randomSingleResult t l) := by
            cases hsa : randomSingleResult s k <;> cases hsb : randomSingleResult t l <;>
              simp only [hsa, hsb, Option.isSome_none, Option.isSome_some] at hsuccess <;>
              first | contradiction | rfl
          have hcall := (random_signer_ct v _ _ _ _ _ _
            ⟨s, t, hs, ht, hca, hcb, hpub, hkeya.trans (hpub.keyLeak.trans hkeyb.symm), by rw [hresa, hresb]; exact hstatus⟩ eac ebc).1
          have hpa := random_post_of_exec (random_signer_retry_pre v hca hfua hf hbound) eac
          have hpb := random_post_of_exec (random_signer_retry_pre v hcb hfub hf hbound) ebc
          rw [hresa] at hpa
          rw [hresb, ← hpub.base, ← hsuccess] at hpb
          have hfinish := (random_callFinish_ct _ _ _ _ _ _ ⟨_, hpa, hpb⟩ eaf ebf).1
          rw [hargs, hcall, hfinish]

end VG.Proof.Dsa.X86_64
