module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Streaming TDEA-CMAC on x86-64: the shared contracts imply ours

The shared contracts with the working space as an argument
(`Proof/CmacTripleDes/StreamScratch.lean`), which `Frame.lean` moves to the
shared contracts of `Spec/Cmac/TripleDesContract.lean`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 16 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 640⟩]

theorem init_implies : initX86_64.Implies (streamInitScratchContract X86_64.abi 0) := by
  sig_implies [streamInitScratchContract, streamInitScratchSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, initX86_64, X86_64.abi, X86_64.argRegs] [initSat] using initSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 688⟩]

theorem absorb_implies : absorbX86_64.Implies (absorbScratchContract X86_64.abi 0) := by
  sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.tdesAbsorbPost, absorbX86_64,
    X86_64.abi, X86_64.argRegs] [absorbSat] using absorbSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem finish_implies : finishX86_64.Implies (finishScratchContract X86_64.abi 0) := by
  sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.tdesFinishPost, finishX86_64,
    X86_64.abi, X86_64.argRegs] [finishSat] using finishSat

end VG.Proof.CmacTripleDes.Stream.X86_64
