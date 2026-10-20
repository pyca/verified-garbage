module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratchW
public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# Streaming TDEA-CMAC on x86: the shared contracts imply ours

The shared contracts with the working space as an argument
(`Proof/CmacTripleDes/StreamScratch.lean`, `StreamScratchW.lean`), which
`Frame.lean` moves to the shared contracts of
`Spec/Cmac/TripleDesContract.lean`: with 20 bytes of stack for
`stream_init` and 24 for `absorb` and `finish` (the arguments they push).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition: the
state at `0x1000`, a 16-byte key at `0x3000` and the scratch buffer at
`0x4000`, as stack arguments at `0x8004`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30 else if a = 0x800c then 16
    else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x3000, 16⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 640⟩]

theorem init_implies : initX86.Implies (streamInitScratchContract X86.abi 20) := by
  have a0 : arg initSat 0 = 0x1000 := by decide
  have a1 : arg initSat 1 = 0x3000 := by decide
  have a2 : arg initSat 2 = 16 := by decide
  have a3 : arg initSat 3 = 0x4000 := by decide
  have e : argAddr initSat 0 = 0x8004 := by decide
  have esp : initSat.gpr .esp = 0x8000 := rfl
  sig_implies [streamInitScratchContract, streamInitScratchSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, initX86]
    [a0, a1, a2, a3, e, esp] using initSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition: the state
at `0x1000`, `count` 0, no data at `0x3000` and the scratch buffer at
`0x4000`, as stack arguments at `0x8004`. -/
def absorbSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8011 then 0x30 else if a = 0x8019 then 0x40 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x8004, 24⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 688⟩]

theorem absorb_implies : absorbX86.Implies (absorbScratchContract X86.abi 24) := by
  have a0 : arg absorbSat 0 = 0x1000 := by decide
  have a1 : arg absorbSat 1 = 0 := by decide
  have a2 : arg absorbSat 2 = 0 := by decide
  have a3 : arg absorbSat 3 = 0x3000 := by decide
  have a4 : arg absorbSat 4 = 0 := by decide
  have a5 : arg absorbSat 5 = 0x4000 := by decide
  have e : argAddr absorbSat 0 = 0x8004 := by decide
  have esp : absorbSat.gpr .esp = 0x8000 := rfl
  sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.tdesAbsorbPost, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, absorbX86, countX86] [a0, a1, a2, a3, a4, a5, e, esp] using absorbSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition: the state
at `0x1000`, `count` 0, `out` at `0x2000` and the scratch buffer at
`0x4000`, as stack arguments at `0x8004`. -/
def finishSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8011 then 0x20 else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x8004, 20⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩, ⟨0x4000, 688⟩]

theorem finish_implies : finishX86.Implies (finishScratchContract86 X86.abi 24) := by
  have a0 : arg finishSat 0 = 0x1000 := by decide
  have a1 : arg finishSat 1 = 0 := by decide
  have a2 : arg finishSat 2 = 0 := by decide
  have a3 : arg finishSat 3 = 0x2000 := by decide
  have a4 : arg finishSat 4 = 0x4000 := by decide
  have e : argAddr finishSat 0 = 0x8004 := by decide
  have esp : finishSat.gpr .esp = 0x8000 := rfl
  sig_implies [finishScratchContract86, finishScratchSig86, Spec.Cmac.tdesFinishPost, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, finishX86, countX86] [a0, a1, a2, a3, a4, e, esp] using finishSat

end VG.Proof.CmacTripleDes.Stream.X86
