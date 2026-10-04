import VerifiedGarbage.Proof.AesOcb.AArch64.Verified
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-!
# AES-OCB on AArch64, with its working space on the stack

Every function runs its code, proved with the working space as its last
argument (`Verified.lean`), in a frame that allocates it. `init`'s working
space is in a register (`x3`): its frame holds the 2560 bytes
(`Verified.stackScratch`). The working space of `seal` and `open` is their
third stack argument, after `tag` and `tag_len`, so their frame of 2592
bytes holds a copy of those two, the address of the working space and the
working space, at the next 16-byte boundary (`Verified.stackArgScratch`).
The code itself uses no stack: its calls keep the return address in `x30`.
`open`'s leak, whether it succeeds, reads only its buffers
(`openLeak_local`).
-/

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.Impl.AesOcb.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- A state satisfying `vg_aes_ocb_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Ocb.initContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Ocb.initContract, Spec.Ocb.initSig, Spec.Ocb.initPre, Spec.Ocb.initPost,
    AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed (v : BlocksImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 2560 .x3 (init (callees v)))
      (Spec.Ocb.initContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Ocb.initPre AArch64.abi.ptrBits) (post := Spec.Ocb.initPost AArch64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2560) (init_verified v) (by decide) (by decide)
    initFrameSat_pre

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ocb.sealContract AArch64.abi 2592).pre s := by
  implies_sat [Spec.Ocb.sealContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Spec.Ocb.sealPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed (v : BlocksImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («seal» (callees v)))
      (Spec.Ocb.sealContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.sealPre AArch64.abi.ptrBits)
    (post := Spec.Ocb.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (seal_verified v) (by decide) (by decide) (Proof.AesOcb.sealPre_local _) (Proof.AesOcb.sealPost_local _)
    sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ocb.openContract AArch64.abi 2592).pre s := by
  implies_sat [Spec.Ocb.openContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Spec.Ocb.openPost,
    Spec.Ocb.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, sealSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed (v : BlocksImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («open» (callees v)))
      (Spec.Ocb.openContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.openPre AArch64.abi.ptrBits)
    (post := Spec.Ocb.openPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Spec.Ocb.openLeak AArch64.abi.ptrBits))
    (open_verified v) (by decide) (by decide) (Proof.AesOcb.openPre_local _)
    (Proof.AesOcb.openPost_local _) openFrameSat_pre (hleak := Proof.AesOcb.openLeak_local _)

end VG.Proof.AesOcb.AArch64
