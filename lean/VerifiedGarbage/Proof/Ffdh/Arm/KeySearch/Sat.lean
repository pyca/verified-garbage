module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
import Mathlib.Util.CompileInductive
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
meta import VerifiedGarbage.TCB.Arm.Target

/-! A concrete legal ARMv7 key-search invocation: a structurally valid
512-bit domain without q and an exhausted initialized retry budget. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Spec.Ffdh

private def keySat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x50 else if a = 0x8005 then 0x30 else if a = 0x8008 then 0x80
    else if a = 0x800C then 0x40 else if a = 0x8011 then 0x70 else if a = 0x8019 then 0x90
    else if a = 0x801C then 0x20 else if a = 0x801D then 4 else if a = 0x8021 then 0x40
    else if a = 0x4010 then 0x40 else if a = 0x3000 then 0x80 else if a = 0x303F then 1
    else if a = 0x307F then 2 else 0
  rd := [⟨0x3000, 128⟩, ⟨0x7000, 0⟩, ⟨0x8000, 36⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x5000, 8⟩, ⟨0x9000, 8448⟩, ⟨0x4000, 128⟩]

theorem sat : ∃ s, (keySearchContract abi stackUse).pre s := by
  refine ⟨keySat, ?_⟩
  sig_iff
  sig_reduce [keySearchContract, keySearchSig, pLenValid, domainLenValid,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
  sig_and_intros
  all_goals first
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel


end VG.Proof.Ffdh.Arm.KeySearch
