module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.InitCT
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.FinishCT
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.AbsorbCT
public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# Streaming TDEA-CMAC on RISC-V: `Verified`

The contracts the proofs are written against (`initRISCV64`,
`absorbRISCV64`, `finishRISCV64`, `Common.lean`), with the working space as
the last argument, which the shared contracts with the working space as an
argument (`Proof/CmacTripleDes/StreamScratch.lean`) imply, with the 944
bytes of stack below the stack pointer that ECB's frame uses: the functions
keep the return address in the working space, and their calls store nothing
in memory.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.Impl.CmacTripleDes.Stream.RISCV64

theorem init_correct (s : State) (hs : initRISCV64.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ initRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := init_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem absorb_correct (s : State) (hs : absorbRISCV64.pre s) :
    ∃ t s', Exec isa absorb s t s' ∧ abiPreserved s s' ∧ absorbRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := absorb_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem finish_correct (s : State) (hs : finishRISCV64.pre s) :
    ∃ t s', Exec isa finish s t s' ∧ abiPreserved s s' ∧ finishRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := finish_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

/-! ## The contracts -/

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a2 => 16 | .a3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 640⟩]

theorem init_implies : initRISCV64.Implies (streamInitScratchContract RISCV64.abi 944) := by
  sig_implies [streamInitScratchContract, streamInitScratchSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, initRISCV64, RISCV64.abi, RISCV64.argRegs] [initSat] using initSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x3000 | .a4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 688⟩]

theorem absorb_implies : absorbRISCV64.Implies (absorbScratchContract RISCV64.abi 944) := by
  sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.tdesAbsorbPost, absorbRISCV64,
    RISCV64.abi, RISCV64.argRegs] [absorbSat] using absorbSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x2000 | .a3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem finish_implies : finishRISCV64.Implies (finishScratchContract RISCV64.abi 944) := by
  sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.tdesFinishPost, finishRISCV64,
    RISCV64.abi, RISCV64.argRegs] [finishSat] using finishSat

theorem init_verified : Verified RISCV64.target streamInit (streamInitScratchContract RISCV64.abi 944) :=
  Verified.of_correct init_correct init_ct init_implies

theorem absorb_verified : Verified RISCV64.target absorb (absorbScratchContract RISCV64.abi 944) :=
  Verified.of_correct absorb_correct absorb_ct absorb_implies

theorem finish_verified : Verified RISCV64.target finish (finishScratchContract RISCV64.abi 944) :=
  Verified.of_correct finish_correct finish_ct finish_implies

end VG.Proof.CmacTripleDes.Stream.RISCV64
