import VerifiedGarbage.Proof.CmacTripleDes.X86.Verified
import VerifiedGarbage.Proof.CmacTripleDes.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/-!
# TDEA-CMAC on x86, with its working space on the stack

The functions run their code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it and copies the arguments
passed on the stack (`Verified.stackScratch`): the return address, the
copied arguments (three for `init`, four for the others) and the 640 bytes
of working space. The copies are read only where the pre- and
postconditions read the buffers (`Proof/CmacTripleDes/Scratch.lean`).
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition, without the
working space: a 16-byte key at `0x1000` and the output at `0x2000`, as
stack arguments at `0x8004`. -/
def initFrameSat : State :=
  { initSat with rd := [⟨0x1000, 16⟩, ⟨0x8004, 12⟩], wr := [⟨0x2000, 400⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesInitContract X86.abi 660).pre s := by
  implies_sat [Spec.Cmac.tdesInitContract, Spec.Cmac.tdesInitSig, Spec.Cmac.tdesInitPre,
    Spec.Cmac.tdesInitPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using initFrameSat

/-- A state satisfying `vg_cmac_triple_des_finalize`'s precondition, without
the working space: the key at `0x1000`, the state at `0x2000` and no last
bytes at `0x3000`, as stack arguments at `0x8004`. -/
def finFrameSat : State :=
  { finSat with rd := [⟨0x1000, 400⟩, ⟨0x3000, 0⟩, ⟨0x8004, 16⟩], wr := [⟨0x2000, 8⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinalizeContract X86.abi 664).pre s := by
  implies_sat [Spec.Cmac.tdesFinalizeContract, Spec.Cmac.tdesFinalizeSig, Spec.Cmac.tdesFinalizePre,
    Spec.Cmac.tdesFinalizePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finFrameSat

/-- A state satisfying `vg_cmac_triple_des_update`'s precondition, without
the working space: as `finFrameSat`, with no blocks. -/
def updFrameSat : State :=
  { finSat with rd := [⟨0x1000, 384⟩, ⟨0x3000, 0⟩, ⟨0x8004, 16⟩], wr := [⟨0x2000, 8⟩] }

theorem updFrameSat_pre : ∃ s, (Spec.Cmac.tdesUpdateContract X86.abi 664).pre s := by
  implies_sat [Spec.Cmac.tdesUpdateContract, Spec.Cmac.tdesUpdateSig, Spec.Cmac.tdesUpdatePost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [updFrameSat, finSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using updFrameSat

theorem init_framed : Verified X86.target (Impl.StackScratch.X86.withStackScratch 660 3 init)
    (Spec.Cmac.tdesInitContract X86.abi 660) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.tdesInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesInitPre X86.abi.ptrBits) (post := Spec.Cmac.tdesInitPost X86.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 660) init_verified (by decide) (by lit_decide) (by lit_decide)
    (initPre_local _) (initPost_local _) initFrameSat_pre

theorem update_framed : Verified X86.target (Impl.StackScratch.X86.withStackScratch 664 4 update)
    (Spec.Cmac.tdesUpdateContract X86.abi 664) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.tdesUpdateSig) (nm := "scratch") (e := .u64) (n := 80)
    (post := Spec.Cmac.tdesUpdatePost X86.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 664) update_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (updatePost_local _) updFrameSat_pre

theorem finalize_framed : Verified X86.target (Impl.StackScratch.X86.withStackScratch 664 4 finalize)
    (Spec.Cmac.tdesFinalizeContract X86.abi 664) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.tdesFinalizeSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesFinalizePre X86.abi.ptrBits)
    (post := Spec.Cmac.tdesFinalizePost X86.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 664) finalize_verified (by decide) (by lit_decide)
    (by lit_decide) (finalizePre_local _) (finalizePost_local _) finFrameSat_pre

end VG.Proof.CmacTripleDes.X86
