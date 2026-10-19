module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverPublicCall
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverContract

/-! # Complete i686 certificate for precomputed PKCS #1 recovery -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131077 then 16
    else if a = 131080 then 16
    else if a = 131085 then 32
    else if a = 131088 then 64
    else if a = 131093 then 48
    else if a = 131096 then 1
    else if a = 131105 then 64
    else if a = 131108 then 64
    else if a = 131113 then 160
    else if a = 131116 then 112
    else if a = 131121 then 80
    else if a = 131124 then 16 else 0
  rd := [⟨8192, 64⟩, ⟨12288, 1⟩, ⟨16384, 64⟩, ⟨20480, 128⟩]
  wr := [⟨4096, 16⟩, ⟨40960, 896⟩, ⟨0x20004, 52⟩]

theorem satisfiable : ∃ s, (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 16 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 12288 := by decide
  have a5 : arg satState 5 = 1 := by decide
  have a6 : arg satState 6 = 0 := by decide
  have a7 : arg satState 7 = 16384 := by decide
  have a8 : arg satState 8 = 64 := by decide
  have a9 : arg satState 9 = 40960 := by decide
  have a10 : arg satState 10 = 112 := by decide
  have a11 : arg satState 11 = 20480 := by decide
  have a12 : arg satState 12 = 16 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  have hash : ∃ h, Spec.RsaPkcs1Sig.Hash.ofId 0 = some h ∧ 16 = h.len := ⟨.md5, rfl, rfl⟩
  sig_implies_sat [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig,
    abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, satState, recoverStack, hash,
      Spec.Rsa.lenValid, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState

theorem recover_verified (v : PublicImpl) :
    Verified target (VG.Impl.RsaPkcs1Sig.X86.Recover.code v.name v.code)
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack) :=
  ⟨recover_contract_correct v, recover_contract_ct v, satisfiable⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv
