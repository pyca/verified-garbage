import VerifiedGarbage.Proof.AesOcb.X86.Verified
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/-!
# AES-OCB on x86, with its working space on the stack

Every function runs its code, proved with the working space as its last
argument (`Verified.lean`), in a frame that allocates it and copies the
arguments passed on the stack (`Verified.stackScratch`): the return address,
the argument slots (ten for `seal` and `open`, three for `init`) and the 2560
bytes of working space, 2608 and 2580 bytes. The code's own calls use 24
bytes below it. The copies are read only where the pre- and postconditions
read the buffers, and `open`'s leak, whether it succeeds, reads only its
buffers (`Proof/AesOcb/Scratch.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.Impl.AesOcb.X86
open VG.Proof.Aes.X86 (BlocksImpl)

theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

variable (v : BlocksImpl)

theorem seal_noEsp : («seal» (callees v)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [«seal», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, tagOut, callBlocks, blocksFrame, callees, Code.allInstrs,
    noEsp_of v.encNosp, noEsp_of v.decNosp, ↓reduceIte]
  decide +kernel

theorem open_noEsp : («open» (callees v)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [«open», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, recv, cmp, mask, callBlocks, blocksFrame, callees, Code.allInstrs,
    noEsp_of v.encNosp, noEsp_of v.decNosp, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_noEsp : (init (callees v)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [init, Impl.AesGcm.X86.entry, keyFrame, blocksFrame, callees, Code.allInstrs, noEsp_of v.encNosp,
    noEsp_of v.expandNosp]
  decide +kernel

theorem seal_stackUse : stackUse («seal» (callees v)) ≤ 24 := by
  simp only [«seal», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, tagOut, callBlocks, blocksFrame, callees, stackUse, v.encStack,
    v.decStack, ↓reduceIte]
  decide +kernel

theorem open_stackUse : stackUse («open» (callees v)) ≤ 24 := by
  simp only [«open», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, recv, cmp, mask, callBlocks, blocksFrame, callees, stackUse,
    v.encStack, v.decStack, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_stackUse : stackUse (init (callees v)) ≤ 24 := by
  simp only [init, Impl.AesGcm.X86.entry, keyFrame, blocksFrame, callees, stackUse, v.encStack, v.expandStack]
  decide +kernel

theorem seal_spSafe : («seal» (callees v)).all (fun i => !isa.writesSp i) = true := by
  simp only [«seal», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, tagOut, callBlocks, blocksFrame, callees, Code.all, v.encSpSafe,
    v.decSpSafe, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem open_spSafe : («open» (callees v)).all (fun i => !isa.writesSp i) = true := by
  simp only [«open», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, recv, cmp, mask, callBlocks, blocksFrame, callees, Code.all,
    v.encSpSafe, v.decSpSafe, Bool.false_eq_true, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem init_spSafe : (init (callees v)).all (fun i => !isa.writesSp i) = true := by
  simp only [init, Impl.AesGcm.X86.entry, keyFrame, blocksFrame, callees, Code.all, v.encSpSafe, v.expandSpSafe,
    Bool.and_true]
  decide +kernel

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space: as `sealSat`, with ten stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x4000, 4⟩, ⟨0x8004, 40⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ocb.sealContract X86.abi 2632).pre s := by
  implies_sat [Spec.Ocb.sealContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Spec.Ocb.sealPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [sealFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using sealFrameSat

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space: as `sealFrameSat`, with the tag read only. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x4000, 4⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x8004, 40⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ocb.openContract X86.abi 2632).pre s := by
  implies_sat [Spec.Ocb.openContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Spec.Ocb.openPost,
    Spec.Ocb.openLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [openFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using openFrameSat

/-- A state satisfying `vg_aes_ocb_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩, ⟨0x8004, 12⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Ocb.initContract X86.abi 2604).pre s := by
  implies_sat [Spec.Ocb.initContract, Spec.Ocb.initSig, Spec.Ocb.initPre, Spec.Ocb.initPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using initFrameSat

theorem seal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2608 10 («seal» (callees v)))
      (Spec.Ocb.sealContract X86.abi 2632) :=
  X86.Verified.stackScratch (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.sealPre X86.abi.ptrBits) (post := Spec.Ocb.sealPost X86.abi.ptrBits)
    (wa := true) (stack := 24) (bytes := 2608) (seal_verified v) (by decide) (seal_noEsp v)
    (seal_stackUse v) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

theorem open_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2608 10 («open» (callees v)))
      (Spec.Ocb.openContract X86.abi 2632) :=
  X86.Verified.stackScratch (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.openPre X86.abi.ptrBits) (post := Spec.Ocb.openPost X86.abi.ptrBits)
    (wa := true) (stack := 24) (leak := some (Spec.Ocb.openLeak X86.abi.ptrBits)) (bytes := 2608)
    (open_verified v) (by decide) (open_noEsp v) (open_stackUse v) (openPre_local _) (openPost_local _)
    openFrameSat_pre (hleak := openLeak_local _)

theorem init_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2580 3 (init (callees v)))
      (Spec.Ocb.initContract X86.abi 2604) :=
  X86.Verified.stackScratch (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Ocb.initPre X86.abi.ptrBits) (post := Spec.Ocb.initPost X86.abi.ptrBits)
    (wa := true) (stack := 24) (bytes := 2580) (init_verified v) (by decide) (init_noEsp v)
    (init_stackUse v) (initPre_local _) (initPost_local _) initFrameSat_pre

end VG.Proof.AesOcb.X86
