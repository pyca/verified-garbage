module
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86_64
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Implies
public import VerifiedGarbage.Impl.StackScratch.X86_64

import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.RoundLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.SboxTables

/-!
# Streaming TDEA-CMAC on x86-64, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratch`): 8 bytes standing for the return address, then
the working space (120 bytes, and 160 for `absorb`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64 VG.Impl.CmacTripleDes.Stream.X86_64

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition,
without the working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 416⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesStreamInitContract X86_64.abi 128).pre s := by
  implies_sat [Spec.Cmac.tdesStreamInitContract, Spec.Cmac.tdesStreamInitSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition, without
the working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 416⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.tdesAbsorbContract X86_64.abi 168).pre s := by
  implies_sat [Spec.Cmac.tdesAbsorbContract, Spec.Cmac.tdesAbsorbSig, Spec.Cmac.tdesAbsorbPost,
    X86_64.abi, X86_64.argRegs] [absorbFrameSat, absorbSat] using absorbFrameSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition, without
the working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinishContract X86_64.abi 128).pre s := by
  implies_sat [Spec.Cmac.tdesFinishContract, Spec.Cmac.tdesFinishSig, Spec.Cmac.tdesFinishPost,
    X86_64.abi, X86_64.argRegs] [finishFrameSat, finishSat] using finishFrameSat

theorem init_framed : Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 128 .rcx streamInit)
    (Spec.Cmac.tdesStreamInitContract X86_64.abi 128) :=
  X86_64.Verified.stackScratch (sig := Spec.Cmac.tdesStreamInitSig) (nm := "scratch") (e := .u64) (n := 15)
    (pre := Spec.Cmac.tdesStreamInitPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.tdesStreamInitPost X86_64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 128) init_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) initFrameSat_pre

theorem absorb_framed : Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 168 .r8 absorb)
    (Spec.Cmac.tdesAbsorbContract X86_64.abi 168) :=
  X86_64.Verified.stackScratch (sig := Spec.Cmac.tdesAbsorbSig) (nm := "scratch") (e := .u64) (n := 20)
    (post := Spec.Cmac.tdesAbsorbPost X86_64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 168) absorb_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) absorbFrameSat_pre

theorem finish_framed : Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 128 .rcx finish)
    (Spec.Cmac.tdesFinishContract X86_64.abi 128) :=
  X86_64.Verified.stackScratch (sig := Spec.Cmac.tdesFinishSig) (nm := "scratch") (e := .u64) (n := 15)
    (post := Spec.Cmac.tdesFinishPost X86_64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 128) finish_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) finishFrameSat_pre

end VG.Proof.CmacTripleDes.Stream.X86_64
