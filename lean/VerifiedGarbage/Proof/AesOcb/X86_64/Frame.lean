import VerifiedGarbage.Proof.AesOcb.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/-!
# AES-OCB on x86-64, with its working space on the stack

Every function runs its code, proved with the working space as its last
argument (`Verified.lean`), in a frame that allocates it. `init`'s working
space is in a register (`rcx`): its frame of 2568 bytes holds the 2560
bytes and 8 more to keep `rsp` aligned (`Verified.stackScratch`). The
working space of `seal` and `open` is passed on the stack after the six
argument registers and four other stack arguments (`data`, `len`, `tag` and
`tag_len`), so their frame of 3632 bytes holds the 3584 bytes of working
space, a copy of those four arguments, the word that stands for the return
address and the address of the working space (`Verified.stackArgScratch`).
The code's own calls use 8 bytes below the frame, the return address, as
`vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch` use
no stack. `open`'s leak, whether it succeeds, reads only its buffers
(`openLeak_local`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

variable (v : BlocksImpl)

theorem init_xdepth : (init (callees v)).x86_64Depth ≤ 8 := by
  simp only [init, callees, Code.x86_64Depth, v.encNoStack, v.expandNoStack]
  decide +kernel

theorem seal_xdepth : («seal» (callees v)).x86_64Depth ≤ 8 := by
  simp only [«seal», front, tagOut, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill,
    hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest, padCk, xorPad, tag, callBlocks, callees,
    Code.x86_64Depth, v.encNoStack, v.decNoStack, ↓reduceIte]
  decide +kernel

theorem open_xdepth : («open» (callees v)).x86_64Depth ≤ 8 := by
  simp only [«open», front, recv, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill,
    hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest, padCk, xorPad, tag, cmp, mask, callBlocks, callees,
    Code.x86_64Depth, v.encNoStack, v.decNoStack, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

/-- A state satisfying `vg_aes_ocb_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Ocb.initContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Ocb.initContract, Spec.Ocb.initSig, Spec.Ocb.initPre, Spec.Ocb.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (init (callees v)))
      (Spec.Ocb.initContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratch (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Ocb.initPre X86_64.abi.ptrBits) (post := Spec.Ocb.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 2568) (init_verified v) (by decide) (by decide)
    (by decide) (init_spSafe v) (init_xdepth v) initFrameSat_pre

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ocb.sealContract X86_64.abi 3640).pre s := by
  implies_sat [Spec.Ocb.sealContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Spec.Ocb.sealPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using sealFrameSat

theorem seal_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 3632 4 («seal» (callees v)))
      (Spec.Ocb.sealContract X86_64.abi 3640) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64)
    (n := 448) (pre := Spec.Ocb.sealPre X86_64.abi.ptrBits)
    (post := Spec.Ocb.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3632) (seal_verified v) (by decide) (by decide) (by decide)
    (seal_spSafe v) (seal_xdepth v) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ocb.openContract X86_64.abi 3640).pre s := by
  implies_sat [Spec.Ocb.openContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Spec.Ocb.openPost,
    Spec.Ocb.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, sealSat] using openFrameSat

theorem open_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 3632 4 («open» (callees v)))
      (Spec.Ocb.openContract X86_64.abi 3640) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64)
    (n := 448) (pre := Spec.Ocb.openPre X86_64.abi.ptrBits)
    (post := Spec.Ocb.openPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.Ocb.openLeak X86_64.abi.ptrBits)) (bytes := 3632) (open_verified v)
    (by decide) (by decide) (by decide) (open_spSafe v) (open_xdepth v) (openPre_local _)
    (openPost_local _) openFrameSat_pre (hleak := openLeak_local _)

end VG.Proof.AesOcb.X86_64
