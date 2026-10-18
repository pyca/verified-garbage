module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptObservations
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptFn
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptFnTiming
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptEntryCache

/-! # Precomputed encryption implements the shared correctness and timing contract -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86

theorem encrypt_contract_correct (v : PublicImpl) (s : State)
    (h : (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encryptStack).pre s) :
    ∃ tr t, Exec isa (VG.Impl.RsaPkcs1Enc.X86.Encrypt.code v.name v.code) s tr t ∧ abiPreserved s t ∧
      (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encryptStack).post s t := by
  have input := encrypt_contract_pre s h
  obtain ⟨tr, t, run, preserved, post⟩ := encryptFn_ok v s input
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig,
    abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  unfold BodyOut at post
  rw [input.enteredCache] at post
  exact post

theorem encrypt_contract_ct (v : PublicImpl) : ConstantTime isa
    (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encryptStack).pre
    (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encryptStack).pub
    (VG.Impl.RsaPkcs1Enc.X86.Encrypt.code v.name v.code) := by
  intro s t tr1 tr2 u w hs ht hp e1 e2
  have is := encrypt_contract_pre s hs
  have it := encrypt_contract_pre t ht
  obtain ⟨exponent, pre⟩ := publicBytes hp
  rw [← publicGeometry hp] at it
  exact (encryptFn_relCT v exponent pre s t tr1 tr2 u w ⟨is, it⟩ e1 e2).1

end VG.Proof.RsaPkcs1Enc.X86.Enc
