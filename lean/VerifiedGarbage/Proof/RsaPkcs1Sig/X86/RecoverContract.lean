module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverPublicCall
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverObservations
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverFn
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverFnTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverContractInput

/-! # Precomputed recovery satisfies the shared correctness and timing contract -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86

theorem recover_contract_correct (v : PublicImpl) (s : State)
    (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pre s) :
    ∃ tr t, Exec isa (VG.Impl.RsaPkcs1Sig.X86.Recover.code v.name v.code) s tr t ∧ abiPreserved s t ∧
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := recoverFn_ok v s (recover_contract_pre s h)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig,
    abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  intro cache hash id
  have out := post cache
  unfold recovered at out
  change Spec.RsaPkcs1Sig.Hash.ofId (arg s 6).toNat = some hash at id
  change Spec.Rsa.written t.mem _ _ _
    ((Spec.RsaPkcs1Sig.Hash.ofId (arg s 6).toNat).bind _) at out
  rw [id, Option.bind_some] at out
  exact out

theorem recover_contract_ct (v : PublicImpl) : ConstantTime isa
    (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pre
    (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pub
    (VG.Impl.RsaPkcs1Sig.X86.Recover.code v.name v.code) := by
  intro s t tr1 tr2 u w hs ht hp e1 e2
  have is := recover_contract_pre s hs
  have it := recover_contract_pre t ht
  rw [← publicGeometry hp, ← publicBytes hp] at it
  exact (recoverFn_relCT v s t tr1 tr2 u w ⟨is, it⟩ e1 e2).1

end VG.Proof.RsaPkcs1Sig.X86.Rcv
