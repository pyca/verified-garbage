import VerifiedGarbage.Proof.AesCcm.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/-!
# AES-CCM on x86-64, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackArgScratch`): their working space is passed on the stack
after the six argument registers and four other stack arguments (`data`,
`len`, `tag` and `tag_len`), so the frame of 2608 bytes holds the 2560 bytes
of working space, a copy of those four arguments, the word that stands for
the return address and the address of the working space. The code's own
calls use 16 bytes below it: the return addresses of the call of
`vg_cmac_aes_update` (or of `vg_aes_ctr32`) and of its call of
`vg_aes_ctr32`, if it makes one (`UpdateImpl.xdepth`), which uses no stack
(`Ctr32Impl.noStack`). `open`'s leak,
whether it succeeds, reads only its buffers (`openLeak_local`).
-/

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.Impl.AesCcm.X86_64
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

variable (v : UpdateImpl)

theorem seal_xdepth : («seal» v.callee v.ctr.callee).x86_64Depth ≤ 16 := by
  have := v.xdepth
  simp only [«seal», sealFront, tagOut, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate,
    callCtr, Code.x86_64Depth, v.ctr.noStack]
  generalize v.callee.code.x86_64Depth = d at this ⊢
  revert d
  decide +kernel

theorem open_xdepth : («open» v.callee v.ctr.callee).x86_64Depth ≤ 16 := by
  have := v.xdepth
  simp only [«open», openFront, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Code.x86_64Depth, v.ctr.noStack]
  generalize v.callee.code.x86_64Depth = d at this ⊢
  revert d
  decide +kernel

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ccm.sealContract X86_64.abi 2624).pre s := by
  implies_sat [Spec.Ccm.sealContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Spec.Ccm.sealPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using sealFrameSat

theorem seal_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («seal» v.callee v.ctr.callee))
      (Spec.Ccm.sealContract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.sealPre X86_64.abi.ptrBits)
    (post := Spec.Ccm.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 2608) (seal_verified v) (by decide) (by decide) (by decide)
    (seal_spSafe v) (seal_xdepth v) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ccm.openContract X86_64.abi 2624).pre s := by
  implies_sat [Spec.Ccm.openContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Spec.Ccm.openPost,
    Spec.Ccm.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, openSat, sealSat] using openFrameSat

theorem open_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («open» v.callee v.ctr.callee))
      (Spec.Ccm.openContract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.openPre X86_64.abi.ptrBits)
    (post := Spec.Ccm.openPost X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (leak := some (Spec.Ccm.openLeak X86_64.abi.ptrBits)) (bytes := 2608) (open_verified v)
    (by decide) (by decide) (by decide) (open_spSafe v) (open_xdepth v) (openPre_local _)
    (openPost_local _) openFrameSat_pre (hleak := openLeak_local _)

end VG.Proof.AesCcm.X86_64
