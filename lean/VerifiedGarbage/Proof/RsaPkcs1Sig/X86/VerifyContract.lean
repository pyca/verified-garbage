module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicCall
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyObservations
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyFn
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyFnTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyContractInput

/-! # The complete precomputed verifier satisfies its shared correctness and timing contract -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86

theorem verify_contract_correct (v : PublicImpl) (s : State)
    (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pre s) :
    ∃ tr t, Exec isa (VG.Impl.RsaPkcs1Sig.X86.Verify.code v.name v.code) s tr t ∧ abiPreserved s t ∧
      (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := verifyFn_ok v s (verify_contract_pre s h)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
    abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact post

theorem verify_contract_ct (v : PublicImpl) : ConstantTime isa
    (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pre
    (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pub
    (VG.Impl.RsaPkcs1Sig.X86.Verify.code v.name v.code) := by
  intro s t tr1 tr2 u w hs ht hp e1 e2
  have is := verify_contract_pre s hs
  have it := verify_contract_pre t ht
  rw [← publicGeometry hp, ← publicBytes hp] at it
  exact (verifyFn_relCT v s t tr1 tr2 u w ⟨is, it⟩ e1 e2).1

end VG.Proof.RsaPkcs1Sig.X86.Ver
