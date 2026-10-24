module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Verified
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs
import VerifiedGarbage.Proof.Framework.SigEval

/-!
# AES-OCB on PPC64LE, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratchArgs`): `tag` and `tag_len` arrive on the stack, so
the frame of 2688 bytes copies them, then the working space's address, above
its stack pointer. The copies are read only where the pre- and
postconditions read the buffers, and `open`'s leak, whether it succeeds,
reads only its buffers (`Proof/AesOcb/Scratch.lean`). As AES-GCM's `open`
(`Proof/AesGcm/PPC64LE/Frame.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x8060, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ocb.sealContract PPC64LE.abi 2688).pre s := by
  implies_sat [Spec.Ocb.sealContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Spec.Ocb.sealPost, PPC64LE.abi,
    PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

theorem seal_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 «seal»)
      (Spec.Ocb.sealContract PPC64LE.abi 2688) :=
  PPC64LE.Verified.stackScratchArgs (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.sealPre PPC64LE.abi.ptrBits) (post := Spec.Ocb.sealPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2688) (m := 2) seal_verified (by decide) (by decide)
    (Proof.AesOcb.sealPre_local _) (Proof.AesOcb.sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8060, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ocb.openContract PPC64LE.abi 2688).pre s := by
  implies_sat [Spec.Ocb.openContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Spec.Ocb.openPost, Spec.Ocb.openLeak,
    PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openFrameSat

theorem open_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 «open»)
      (Spec.Ocb.openContract PPC64LE.abi 2688) :=
  PPC64LE.Verified.stackScratchArgs (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.openPre PPC64LE.abi.ptrBits) (post := Spec.Ocb.openPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2688) (m := 2) (leak := some (Spec.Ocb.openLeak PPC64LE.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.AesOcb.openPre_local _) (Proof.AesOcb.openPost_local _)
    openFrameSat_pre (hleak := Proof.AesOcb.openLeak_local _)

end VG.Proof.AesOcb.PPC64LE
