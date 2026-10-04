import VerifiedGarbage.Proof.AesCcm.AArch64.Verified
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-!
# AES-CCM on AArch64, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackArgScratch`): their working space is their third stack
argument, after `tag` and `tag_len`, so the frame of 2592 bytes holds a copy
of those two, the address of the working space and the working space, at the
next 16-byte boundary. The code itself uses no stack: its calls keep the
return address in `x30`. `open`'s leak, whether it succeeds, reads only its
buffers (`openLeak_local`).
-/

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.Impl.AesCcm.AArch64

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ccm.sealContract AArch64.abi 2592).pre s := by
  implies_sat [Spec.Ccm.sealContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Spec.Ccm.sealPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («seal» v.callee v.ctr.callee))
      (Spec.Ccm.sealContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.sealPre AArch64.abi.ptrBits)
    (post := Spec.Ccm.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (seal_verified v) (by decide) (by decide) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ccm.openContract AArch64.abi 2592).pre s := by
  implies_sat [Spec.Ccm.openContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Spec.Ccm.openPost,
    Spec.Ccm.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, openSat, sealSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («open» v.callee v.ctr.callee))
      (Spec.Ccm.openContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.openPre AArch64.abi.ptrBits)
    (post := Spec.Ccm.openPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Spec.Ccm.openLeak AArch64.abi.ptrBits))
    (open_verified v) (by decide) (by decide) (openPre_local _) (openPost_local _) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesCcm.AArch64
