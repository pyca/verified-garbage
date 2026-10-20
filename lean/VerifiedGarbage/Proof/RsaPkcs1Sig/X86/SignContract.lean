module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateCall
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignObservations
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignFn
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignFnTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignContractInput
import VerifiedGarbage.Proof.Rsa.X86.PrivObservations

/-! # PKCS #1 signing implements the shared contract and permitted leakage -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode)

theorem sign_contract_correct (v : CrtImpl) (s : State)
    (h : (Spec.RsaPkcs1Sig.signContract abi sigStack).pre s) :
    ∃ tr t, Exec isa (VG.Impl.RsaPkcs1Sig.X86.Sign.code (privName v) (privCode v)) s tr t ∧
      abiPreserved s t ∧ (Spec.RsaPkcs1Sig.signContract abi sigStack).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := signFn_ok v s (sign_contract_pre s h)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact post

theorem sign_contract_ct (v : CrtImpl) : ConstantTime isa (Spec.RsaPkcs1Sig.signContract abi sigStack).pre
    (Spec.RsaPkcs1Sig.signContract abi sigStack).pub
    (VG.Impl.RsaPkcs1Sig.X86.Sign.code (privName v) (privCode v)) := by
  intro s t tr1 tr2 u w hs ht hp e1 e2
  have is := sign_contract_pre s hs
  have it := sign_contract_pre t ht
  obtain ⟨nb, eb⟩ := publicBytes hp
  rw [← publicGeometry hp] at it
  exact (signFn_relCT v nb eb s t tr1 tr2 u w ⟨is, it⟩ e1 e2).1

end VG.Proof.RsaPkcs1Sig.X86.Sgn
