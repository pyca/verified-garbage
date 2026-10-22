module

import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.CT
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.ABI
public import VerifiedGarbage.Impl.Ffdh.X86.KeySearch
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Sig

/-! # `vg_ffdh_generate_key_search` on i686 against its contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86

/-- x, y of 64 bytes, `used`, a structurally valid 512-bit domain without q (`p = 2⁵¹¹ + 1`, `g = 2`), an
empty tape, a working space of 1056 words and a state with the width 64, apart. -/
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
    else if a = 0x20015 then 0x50
    else if a = 0x20019 then 0x30
    else if a = 0x2001c then 128
    else if a = 0x20020 then 64
    else if a = 0x20025 then 0x40
    else if a = 0x2002d then 0x90
    else if a = 0x20030 then 0x20
    else if a = 0x20031 then 4
    else if a = 0x20035 then 0x60
    else if a = 0x6010 then 64
    else if a = 0x3000 then 0x80
    else if a = 0x303F then 1
    else if a = 0x307F then 2 else 0
  rd := [⟨0x3000, 128⟩, ⟨0x4000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x5000, 8⟩, ⟨0x9000, 8448⟩, ⟨0x6000, 128⟩, ⟨0x20004, 52⟩]

theorem satisfiable : ∃ s, (Spec.Ffdh.keySearchContract abi stack).pre s := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 0x2000 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 0x5000 := by decide
  have a5 : arg satState 5 = 0x3000 := by decide
  have a6 : arg satState 6 = 128 := by decide
  have a7 : arg satState 7 = 64 := by decide
  have a8 : arg satState 8 = 0x4000 := by decide
  have a9 : arg satState 9 = 0 := by decide
  have a10 : arg satState 10 = 0x9000 := by decide
  have a11 : arg satState 11 = 1056 := by decide
  have a12 : arg satState 12 = 0x6000 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  refine ⟨satState, ?_⟩
  sig_pre [Spec.Ffdh.keySearchContract, Spec.Ffdh.keySearchSig, abi, argSlots, argVal, argBytes, stackBelow,
    Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e]
  sig_and_intros
  all_goals first
    | exact Region.disjoint_of_sep (by decide)
    | decide +kernel

theorem verified : Verified target Impl.Ffdh.X86.KeySearch.code (Spec.Ffdh.keySearchContract abi stack) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Ffdh.X86.KeySearch
