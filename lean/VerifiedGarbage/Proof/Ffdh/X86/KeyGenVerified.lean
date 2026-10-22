module

import VerifiedGarbage.Proof.Ffdh.X86.KeyGenCT
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.Ffdh.X86.KeyGen
public import VerifiedGarbage.Proof.Ffdh.X86.ABI

/-! # `vg_ffdh_generate_key` on i686 against its contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeyGen

open VG VG.X86

/-- x, y and `rand` of 64 bytes, a domain of 128 and a working space of 1056 words, apart. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 0x10
    else if a = 0x20008 then 64
    else if a = 0x2000d then 0x20
    else if a = 0x20010 then 64
    else if a = 0x20015 then 0x30
    else if a = 0x20018 then 128
    else if a = 0x2001c then 64
    else if a = 0x20021 then 0x40
    else if a = 0x20024 then 64
    else if a = 0x20029 then 0x90
    else if a = 0x2002c then 0x20
    else if a = 0x2002d then 4 else 0
  rd := [⟨0x3000, 128⟩, ⟨0x4000, 64⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x9000, 8448⟩, ⟨0x20004, 44⟩]

theorem satisfiable : ∃ s, (Spec.Ffdh.generateKeyContract abi stack).pre s := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 0x2000 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 0x3000 := by decide
  have a5 : arg satState 5 = 128 := by decide
  have a6 : arg satState 6 = 64 := by decide
  have a7 : arg satState 7 = 0x4000 := by decide
  have a8 : arg satState 8 = 64 := by decide
  have a9 : arg satState 9 = 0x9000 := by decide
  have a10 : arg satState 10 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argSlots, argVal, argBytes,
    stackBelow, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp, satState, Spec.Rsa.scratchWords] using satState

theorem verified : Verified target Impl.Ffdh.X86.GenerateKey.code (Spec.Ffdh.generateKeyContract abi stack) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Ffdh.X86.KeyGen
