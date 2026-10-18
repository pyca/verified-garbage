module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptContract

/-! # Complete i686 certificate for precomputed PKCS #1 encryption -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131077 then 16
    else if a = 131080 then 64
    else if a = 131085 then 32
    else if a = 131088 then 64
    else if a = 131093 then 48
    else if a = 131096 then 1
    else if a = 131101 then 64
    else if a = 131109 then 80
    else if a = 131112 then 61
    else if a = 131117 then 160
    else if a = 131120 then 112
    else if a = 131125 then 96
    else if a = 131128 then 16 else 0
  rd := [⟨8192, 64⟩, ⟨12288, 1⟩, ⟨16384, 0⟩, ⟨20480, 61⟩, ⟨24576, 128⟩]
  wr := [⟨4096, 64⟩, ⟨40960, 896⟩, ⟨0x20004, 56⟩]

theorem satisfiable : ∃ s, (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encryptStack).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 12288 := by decide
  have a5 : arg satState 5 = 1 := by decide
  have a6 : arg satState 6 = 16384 := by decide
  have a7 : arg satState 7 = 0 := by decide
  have a8 : arg satState 8 = 20480 := by decide
  have a9 : arg satState 9 = 61 := by decide
  have a10 : arg satState 10 = 40960 := by decide
  have a11 : arg satState 11 = 112 := by decide
  have a12 : arg satState 12 = 24576 := by decide
  have a13 : arg satState 13 = 16 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig,
    abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, e, esp, satState, encryptStack,
      Spec.Rsa.lenValid, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState

theorem encrypt_verified (v : PublicImpl) :
    Verified target (VG.Impl.RsaPkcs1Enc.X86.Encrypt.code v.name v.code)
      (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encryptStack) :=
  ⟨encrypt_contract_correct v, encrypt_contract_ct v, satisfiable⟩

end VG.Proof.RsaPkcs1Enc.X86.Enc
