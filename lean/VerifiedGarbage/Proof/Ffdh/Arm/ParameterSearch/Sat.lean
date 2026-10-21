module

public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
import Mathlib.Util.CompileInductive
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.GenerationContract
meta import VerifiedGarbage.TCB.Arm.Target

/-! The unchanged public search contract admits a concrete ARMv7 call. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

private def searchSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x1100 | .r3 => 512 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 2 else if a = 0x8005 then 0x20 else if a = 0x800d then 0x30 else
    if a = 0x8010 then 0x20 else if a = 0x8011 then 4 else if a = 0x8015 then 0x60 else
    if a = 0x6008 then 0x40 else if a = 0x6010 then 0x40 else if a = 0x6012 then 0x20 else 0
  rd := [⟨0x2000, 0⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x3000, 8448⟩, ⟨0x6000, 128⟩]

theorem search_sat : ∃ s, (Spec.Ffdh.parameterSearchContract abi 232).pre s := by
  sig_implies_sat [Spec.Ffdh.parameterSearchContract, Spec.Ffdh.parameterSearchSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
    [searchSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords,
      Spec.Ffdh.parameterAttempts, Spec.Ffdh.parameterEntropy] using searchSat

end VG.Proof.Ffdh.Arm.ParameterSearch
