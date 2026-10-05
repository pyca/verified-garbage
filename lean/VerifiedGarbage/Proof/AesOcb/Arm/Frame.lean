import VerifiedGarbage.Proof.AesOcb.Arm.Verified
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# AES-OCB on ARMv7, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratch`): their working space is their seventh stack
argument, after `aad`, `aad_len`, `data`, `len`, `tag` and `tag_len`, so the
frame of 2592 bytes holds a copy of those six words, the address of the
working space, the saved `lr` and the working space. The copies are read
only where the pre- and postconditions read the buffers, and `open`'s leak,
whether it succeeds, reads only its buffers (`Proof/AesOcb/Scratch.lean`).
-/

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Impl.AesOcb.Arm

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ocb.sealContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Ocb.sealContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Spec.Ocb.sealPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «seal»)
      (Spec.Ocb.sealContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.sealPre Arm.abi.ptrBits)
    (post := Spec.Ocb.sealPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 6) seal_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.AesOcb.sealPre_local _) (Proof.AesOcb.sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ocb.openContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Ocb.openContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Spec.Ocb.openPost,
    Spec.Ocb.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem open_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «open»)
      (Spec.Ocb.openContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.openPre Arm.abi.ptrBits)
    (post := Spec.Ocb.openPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.Ocb.openLeak Arm.abi.ptrBits))
    (m := 6) open_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.AesOcb.openPre_local _) (Proof.AesOcb.openPost_local _) openFrameSat_pre
    (hleak := Proof.AesOcb.openLeak_local _)

end VG.Proof.AesOcb.Arm
