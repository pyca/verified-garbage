module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# Streaming TDEA-CMAC on ARMv7: the shared contracts imply ours

The shared contracts with the working space as an argument
(`Proof/CmacTripleDes/StreamScratch.lean`), which `Frame.lean` moves to the
shared contracts of `Spec/Cmac/TripleDesContract.lean`: with no stack for
`stream_init`, and 4 bytes for `absorb` and `finish` (the stack argument
they push).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r2 => 16 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 640⟩]

theorem init_implies : initArm.Implies (streamInitScratchContract Arm.abi 0) := by
  sig_implies [streamInitScratchContract, streamInitScratchSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, initArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [initSat] using initSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition (with no
data): `state` at `0x1000`, `data` at `0x3000`, `scratch` at `0x4000`, the
stack arguments at `0x8000`. -/
def absorbSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else if a = 0x8009 then 0x40 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x8000, 12⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 688⟩]

theorem absorb_implies : absorbArm.Implies (absorbScratchContract Arm.abi 4) := by
  sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.tdesAbsorbPost, absorbArm, countArm,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using absorbSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition: `state` at
`0x1000`, `out` at `0x2000`, `scratch` at `0x4000`, the stack arguments at
`0x8000`. -/
def finishSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x20 else if a = 0x8005 then 0x40 else 0
  rd := [⟨0x8000, 8⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem finish_implies : finishArm.Implies (finishScratchContract Arm.abi 4) := by
  sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.tdesFinishPost, finishArm, countArm,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finishSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using finishSat

end VG.Proof.CmacTripleDes.Stream.Arm
