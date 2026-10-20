module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateCall
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignContract
import VerifiedGarbage.Proof.Rsa.X86.PrivVerified
import VerifiedGarbage.Proof.Framework.Contract

/-! # Complete i686 certificate for checked PKCS #1 signing -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode)

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
    else if a = 131105 then 64
    else if a = 131108 then 64
    else if a = 131113 then 80
    else if a = 131116 then 1
    else if a = 131121 then 96
    else if a = 131124 then 1
    else if a = 131129 then 112
    else if a = 131132 then 1
    else if a = 131137 then 128
    else if a = 131140 then 1
    else if a = 131145 then 144
    else if a = 131148 then 1
    else if a = 131153 then 160
    else if a = 131156 then 32
    else if a = 131157 then 4 else 0
  rd := [⟨8192, 64⟩, ⟨12288, 1⟩, ⟨16384, 64⟩, ⟨20480, 1⟩, ⟨24576, 1⟩, ⟨28672, 1⟩, ⟨32768, 1⟩, ⟨36864, 1⟩]
  wr := [⟨4096, 64⟩, ⟨40960, 8448⟩, ⟨0x20004, 84⟩]

theorem satisfiable : ∃ s, (Spec.RsaPkcs1Sig.signContract abi sigStack).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 12288 := by decide
  have a5 : arg satState 5 = 1 := by decide
  have a6 : arg satState 6 = 0 := by decide
  have a7 : arg satState 7 = 16384 := by decide
  have a8 : arg satState 8 = 64 := by decide
  have a9 : arg satState 9 = 20480 := by decide
  have a10 : arg satState 10 = 1 := by decide
  have a11 : arg satState 11 = 24576 := by decide
  have a12 : arg satState 12 = 1 := by decide
  have a13 : arg satState 13 = 28672 := by decide
  have a14 : arg satState 14 = 1 := by decide
  have a15 : arg satState 15 = 32768 := by decide
  have a16 : arg satState 16 = 1 := by decide
  have a17 : arg satState 17 = 36864 := by decide
  have a18 : arg satState 18 = 1 := by decide
  have a19 : arg satState 19 = 40960 := by decide
  have a20 : arg satState 20 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, e, esp, satState, sigStack,
      Spec.Rsa.lenValid, Spec.Rsa.scratchWords] using satState

theorem sign_verified (v : CrtImpl) :
    Verified target (VG.Impl.RsaPkcs1Sig.X86.Sign.code (privName v) (privCode v))
      (Spec.RsaPkcs1Sig.signContract abi sigStack) :=
  ⟨sign_contract_correct v, sign_contract_ct v, satisfiable⟩

end VG.Proof.RsaPkcs1Sig.X86.Sgn
