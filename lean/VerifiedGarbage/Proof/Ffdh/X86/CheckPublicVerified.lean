module

import VerifiedGarbage.Proof.Ffdh.X86.CheckPublicCT
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
public import VerifiedGarbage.Proof.Ffdh.X86.ABI
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! # `vg_ffdh_check_public` on i686 against its contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.CheckPublic

open VG VG.X86

theorem correct (s : State) (h : (Spec.Ffdh.checkPublicContract abi stack).pre s) :
    ∃ trace t, Exec isa Impl.Ffdh.X86.CheckPublic.code s trace t ∧ abiPreserved s t ∧
      (Spec.Ffdh.checkPublicContract abi stack).post s t := by
  obtain ⟨trace, t, E, V, P⟩ := operation_ok (checkPublicABI_of h)
  refine ⟨trace, t, E, P, ?_⟩
  sig_post [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact V

/-- A domain of 128 bytes, `p_len` 64, y of 64 bytes and a working space of 1056 words, apart. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 0x20
    else if a = 0x20008 then 128
    else if a = 0x2000c then 64
    else if a = 0x20011 then 0x30
    else if a = 0x20014 then 64
    else if a = 0x20019 then 0x90
    else if a = 0x2001c then 0x20
    else if a = 0x2001d then 4 else 0
  rd := [⟨8192, 128⟩, ⟨12288, 64⟩]
  wr := [⟨36864, 8448⟩, ⟨0x20004, 28⟩]

theorem satisfiable : ∃ s, (Spec.Ffdh.checkPublicContract abi stack).pre s := by
  have a0 : arg satState 0 = 8192 := by decide
  have a1 : arg satState 1 = 128 := by decide
  have a2 : arg satState 2 = 64 := by decide
  have a3 : arg satState 3 = 12288 := by decide
  have a4 : arg satState 4 = 64 := by decide
  have a5 : arg satState 5 = 36864 := by decide
  have a6 : arg satState 6 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argSlots, argVal, argBytes,
    stackBelow, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
    [a0, a1, a2, a3, a4, a5, a6, e, esp, satState, Spec.Rsa.scratchWords] using satState

theorem verified : Verified target Impl.Ffdh.X86.CheckPublic.code (Spec.Ffdh.checkPublicContract abi stack) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Ffdh.X86.CheckPublic
