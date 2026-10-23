module

import VerifiedGarbage.Proof.Ffdh.X86.DeriveCT
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.Ffdh.X86.Derive
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Ffdh.X86.ABI

/-! # `vg_ffdh_derive_public` on i686 against its contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Derive

open VG VG.X86

/-- An output of 64 bytes, a domain of 128, `p_len` 64, x of one byte and a working space of 1056 words,
apart. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 0x10
    else if a = 0x20008 then 64
    else if a = 0x2000d then 0x20
    else if a = 0x20010 then 128
    else if a = 0x20014 then 64
    else if a = 0x20019 then 0x40
    else if a = 0x2001c then 1
    else if a = 0x20021 then 0x90
    else if a = 0x20024 then 0x20
    else if a = 0x20025 then 4 else 0
  rd := [⟨8192, 128⟩, ⟨16384, 1⟩]
  wr := [⟨4096, 64⟩, ⟨36864, 8448⟩, ⟨0x20004, 36⟩]

theorem satisfiable : ∃ s, (Spec.Ffdh.derivePublicContract abi stack).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 128 := by decide
  have a4 : arg satState 4 = 64 := by decide
  have a5 : arg satState 5 = 16384 := by decide
  have a6 : arg satState 6 = 1 := by decide
  have a7 : arg satState 7 = 36864 := by decide
  have a8 : arg satState 8 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argSlots, argVal, argBytes,
    stackBelow, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp, satState, Spec.Rsa.scratchWords] using satState

theorem verified : Verified target Impl.Ffdh.X86.DerivePublic.code (Spec.Ffdh.derivePublicContract abi stack) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Ffdh.X86.Derive
