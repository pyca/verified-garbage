module
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Implies
public import VerifiedGarbage.Impl.StackScratch.X86

import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Verified
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.CmacTripleDes.X86.Lit
import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.SboxTables

/-!
# Streaming TDEA-CMAC on x86, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it and copies the
arguments passed on the stack (`Verified.stackScratch`): the return address,
the copied argument slots (three for `stream_init`, five for `absorb`, four
for `finish`) and the working space (640 bytes for `stream_init`, 688 for
the others). The copies are read only where the pre- and postconditions
read the buffers (`Proof/CmacTripleDes/StreamScratch.lean`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86 VG.Impl.CmacTripleDes.Stream.X86

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition,
without the working space: the state at `0x1000` and a 16-byte key at
`0x3000`, as stack arguments at `0x8004`. -/
def initFrameSat : State :=
  { initSat with rd := [⟨0x3000, 16⟩, ⟨0x8004, 12⟩], wr := [⟨0x1000, 416⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesStreamInitContract X86.abi 680).pre s := by
  implies_sat [Spec.Cmac.tdesStreamInitContract, Spec.Cmac.tdesStreamInitSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using initFrameSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition, without
the working space: as `absorbSat`. -/
def absorbFrameSat : State :=
  { absorbSat with rd := [⟨0x3000, 0⟩, ⟨0x8004, 20⟩], wr := [⟨0x1000, 416⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.tdesAbsorbContract X86.abi 740).pre s := by
  implies_sat [Spec.Cmac.tdesAbsorbContract, Spec.Cmac.tdesAbsorbSig, Spec.Cmac.tdesAbsorbPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [absorbFrameSat, absorbSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using absorbFrameSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition, without
the working space: as `finishSat`. -/
def finishFrameSat : State :=
  { finishSat with rd := [⟨0x8004, 16⟩], wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinishContract X86.abi 736).pre s := by
  implies_sat [Spec.Cmac.tdesFinishContract, Spec.Cmac.tdesFinishSig, Spec.Cmac.tdesFinishPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finishFrameSat, finishSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finishFrameSat

theorem init_framed : Verified X86.target (Impl.StackScratch.X86.withStackScratch 660 3 streamInit)
    (Spec.Cmac.tdesStreamInitContract X86.abi 680) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.tdesStreamInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesStreamInitPre X86.abi.ptrBits) (post := Spec.Cmac.tdesStreamInitPost X86.abi.ptrBits)
    (wa := false) (stack := 20) (bytes := 660) init_verified (by decide) (by lit_decide) (by lit_decide)
    (streamInitPre_local _) (streamInitPost_local _) initFrameSat_pre

theorem absorb_framed : Verified X86.target (Impl.StackScratch.X86.withStackScratch 716 5 absorb)
    (Spec.Cmac.tdesAbsorbContract X86.abi 740) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.tdesAbsorbSig) (nm := "scratch") (e := .u64) (n := 86)
    (post := Spec.Cmac.tdesAbsorbPost X86.abi.ptrBits)
    (wa := false) (stack := 24) (bytes := 716) absorb_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (absorbPost_local _) absorbFrameSat_pre

theorem finish_framed : Verified X86.target (Impl.StackScratch.X86.withStackScratch 712 4 finish)
    (Spec.Cmac.tdesFinishContract X86.abi 736) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.tdesFinishSig) (nm := "scratch") (e := .u64) (n := 86)
    (post := Spec.Cmac.tdesFinishPost X86.abi.ptrBits)
    (wa := false) (stack := 24) (bytes := 712) finish_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (finishPost_local _) finishFrameSat_pre

end VG.Proof.CmacTripleDes.Stream.X86
