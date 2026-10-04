import VerifiedGarbage.Proof.AesCcm.Arm.Verified
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# AES-CCM on ARMv7, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratch`): their working space is their seventh stack
argument, after `aad`, `aad_len`, `data`, `len`, `tag` and `tag_len`, so the
frame of 2592 bytes holds a copy of those six words, the address of the
working space, the saved `lr` and the working space. The copies are read
only where the pre- and postconditions read the buffers, and `open`'s leak,
whether it succeeds, reads only its buffers (`Proof/AesCcm/Scratch.lean`).
-/

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ccm.sealContract Arm.abi 2608).pre s := by
  implies_sat [Spec.Ccm.sealContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Spec.Ccm.sealPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «seal»)
      (Spec.Ccm.sealContract Arm.abi 2608) :=
  Arm.Verified.stackScratch (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.sealPre Arm.abi.ptrBits)
    (post := Spec.Ccm.sealPost Arm.abi.ptrBits) (wa := true) (stack := 16)
    (m := 6) seal_verified (by decide) (by decide) (by decide) (by decide)
    (sealPre_local _) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ccm.openContract Arm.abi 2608).pre s := by
  implies_sat [Spec.Ccm.openContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Spec.Ccm.openPost,
    Spec.Ccm.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem open_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «open»)
      (Spec.Ccm.openContract Arm.abi 2608) :=
  Arm.Verified.stackScratch (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.openPre Arm.abi.ptrBits)
    (post := Spec.Ccm.openPost Arm.abi.ptrBits) (wa := true) (stack := 16)
    (leak := some (Spec.Ccm.openLeak Arm.abi.ptrBits))
    (m := 6) open_verified (by decide) (by decide) (by decide) (by decide)
    (openPre_local _) (openPost_local _) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesCcm.Arm
