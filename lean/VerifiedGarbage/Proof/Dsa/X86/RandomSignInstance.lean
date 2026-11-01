module

public import VerifiedGarbage.Proof.Dsa.X86.Verified
public import VerifiedGarbage.Impl.Dsa.X86.RandomSign
public import VerifiedGarbage.Proof.Dsa.X86.RandomCall
public import VerifiedGarbage.Proof.Framework.X86.CallWith

import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCT
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
/-! # The randomized signer, calling the registered `vg_dsa_sign` (x86) -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/RandomSignVerified.lean`, which only this module imported.
section

/-! # The x86 randomized signer meets its contract -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86.RandomSign

/-- A disjoint 1024/160 call with an empty tape. -/
def randomSignSatState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 0x10 else if a = 0x20008 then 40 else if a = 0x2000d then 0x70
    else if a = 0x20011 then 0x20 else if a = 0x20014 then 0xa8 else if a = 0x20015 then 1
    else if a = 0x20018 then 128 else if a = 0x2001c then 20 else if a = 0x20021 then 0x50
    else if a = 0x20029 then 0x60 else if a = 0x20031 then 0x80 else if a = 0x20034 then 0x40
    else if a = 0x20035 then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x5000, 0⟩, ⟨0x6000, 0⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x7000, 8⟩, ⟨0x8000, 16896⟩, ⟨0x20004, 52⟩]

theorem randomSign_satisfiable : ∃ s, (Spec.Dsa.randomSignContract abi 232).pre s := by
  have a0 : arg randomSignSatState 0 = 0x1000 := by decide
  have a1 : arg randomSignSatState 1 = 40 := by decide
  have a2 : arg randomSignSatState 2 = 0x7000 := by decide
  have a3 : arg randomSignSatState 3 = 0x2000 := by decide
  have a4 : arg randomSignSatState 4 = 424 := by decide
  have a5 : arg randomSignSatState 5 = 128 := by decide
  have a6 : arg randomSignSatState 6 = 20 := by decide
  have a7 : arg randomSignSatState 7 = 0x5000 := by decide
  have a8 : arg randomSignSatState 8 = 0 := by decide
  have a9 : arg randomSignSatState 9 = 0x6000 := by decide
  have a10 : arg randomSignSatState 10 = 0 := by decide
  have a11 : arg randomSignSatState 11 = 0x8000 := by decide
  have a12 : arg randomSignSatState 12 = 2112 := by decide
  have e : argAddr randomSignSatState 0 = 0x20004 := by decide
  have esp : randomSignSatState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes,
    stackBelow] [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, randomSignSatState]
    using randomSignSatState

theorem randomSign_verified (F : SignFn) :
    Verified target (code F.name F.code) (Spec.Dsa.randomSignContract abi 232) :=
  ⟨randomSign_correct F, randomSign_constantTime F, randomSign_satisfiable⟩

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

/-- The supplied-nonce signer, as registered. -/
def signFn : SignFn where
  name := "vg_dsa_sign"
  code := Entry.operation true
  verified := signing_verified
  noSp := NoSp.of_all (by decide +kernel)
  depth := by decide +kernel

theorem randomSigning_verified :
    Verified target (RandomSign.code signFn.name signFn.code) (Spec.Dsa.randomSignContract abi 232) :=
  randomSign_verified signFn

end VG.Proof.Dsa.X86
