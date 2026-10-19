module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyContract

/-! # Complete i686 certificate for precomputed PKCS #1 verification -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131077 then 32
    else if a = 131080 then 64
    else if a = 131085 then 48
    else if a = 131088 then 1
    else if a = 131097 then 64
    else if a = 131100 then 16
    else if a = 131105 then 80
    else if a = 131108 then 64
    else if a = 131113 then 160
    else if a = 131116 then 112
    else if a = 131121 then 96
    else if a = 131124 then 16 else 0
  rd := [⟨8192, 64⟩, ⟨12288, 1⟩, ⟨16384, 16⟩, ⟨20480, 64⟩, ⟨24576, 128⟩]
  wr := [⟨40960, 896⟩, ⟨0x20004, 52⟩]

theorem satisfiable : ∃ s, (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pre s := by
  have a0 : arg satState 0 = 8192 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 12288 := by decide
  have a3 : arg satState 3 = 1 := by decide
  have a4 : arg satState 4 = 0 := by decide
  have a5 : arg satState 5 = 16384 := by decide
  have a6 : arg satState 6 = 16 := by decide
  have a7 : arg satState 7 = 20480 := by decide
  have a8 : arg satState 8 = 64 := by decide
  have a9 : arg satState 9 = 40960 := by decide
  have a10 : arg satState 10 = 112 := by decide
  have a11 : arg satState 11 = 24576 := by decide
  have a12 : arg satState 12 = 16 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
    abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, satState, verifyStack,
      Spec.Rsa.lenValid, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState

theorem verify_verified (v : PublicImpl) :
    Verified target (VG.Impl.RsaPkcs1Sig.X86.Verify.code v.name v.code)
      (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack) :=
  ⟨verify_contract_correct v, verify_contract_ct v, satisfiable⟩

end VG.Proof.RsaPkcs1Sig.X86.Ver
