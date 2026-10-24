module

public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Verified
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Scratch
import VerifiedGarbage.Proof.Sm4Gcm.Scratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs
import VerifiedGarbage.Proof.Framework.SigEval

/-!
# SM4-GCM on PPC64LE, with its working spaces on the stack

Each function runs its code, proved with AES-GCM's working space and SM4's
as its last two arguments (`Verified.lean`), in two frames: the inner one
allocates SM4's (3296 bytes), the outer one AES-GCM's (2592 bytes), each
less than a page (`Verified.stackScratch`). The inner frame's contract is
the function's with AES-GCM's working space as one more argument, which the
pre- and postcondition ignore (`Scratch.lean`). For `seal` and `open`, whose
working spaces arrive on the stack, each frame also copies the stack
arguments before them (`Verified.stackScratchArgs`): 2672 and 3376 bytes for
`seal`, 2672 and 3392 for `open`.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE

/-! ## `init` -/

def initInnerSat : State := { initSat with wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩] }

theorem initInnerSat_pre : ∃ s, ((Spec.Sm4.Gcm.initSig.withScratch "scratch" .u64 320).contract PPC64LE.abi
    (Curry.withScratch PPC64LE.abi.ptrBits "scratch" .u64 320 Spec.Sm4.Gcm.initSig.params
      (Curry.const (fun _ => True) _))
    (Curry.withScratch PPC64LE.abi.ptrBits "scratch" .u64 320 Spec.Sm4.Gcm.initSig.params
      (Spec.Sm4.Gcm.initPost PPC64LE.abi.ptrBits)) true (0 + 3296)).pre s := by
  implies_sat [Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost,
    PPC64LE.abi, PPC64LE.argRegs] [initInnerSat, initSat] using initInnerSat

def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.initContract PPC64LE.abi 5888).pre s := by
  implies_sat [Spec.Sm4.Gcm.initContract, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost, PPC64LE.abi,
    PPC64LE.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r5
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r6 init))
      (Spec.Sm4.Gcm.initContract PPC64LE.abi 5888) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.initPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 3296) (bytes := 2592)
    (PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.initSig.withScratch "scratch" .u64 320) (nm := "sm4")
      (e := .u64) (n := 408) (wa := true) (stack := 0) (bytes := 3296) init_verified (by decide) (by decide)
      (pre_withScratch "scratch" .u64 320 (Proof.Sm4Gcm.pre_local _ _))
      (post_withScratch "scratch" .u64 320 (Proof.Sm4Gcm.initPost_local _)) initInnerSat_pre)
    (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.initPost_local _) initFrameSat_pre

/-! ## `stream_encrypt` -/

def streamEncryptInnerSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩] }

theorem streamEncryptInnerSat_pre : ∃ s, ((Spec.Sm4.Gcm.streamCryptSig.withScratch "scratch" .u64 320).contract PPC64LE.abi
    (Curry.withScratch PPC64LE.abi.ptrBits "scratch" .u64 320 Spec.Sm4.Gcm.streamCryptSig.params (Curry.const (fun _ => True) _))
    (Curry.withScratch PPC64LE.abi.ptrBits "scratch" .u64 320 Spec.Sm4.Gcm.streamCryptSig.params (Spec.Sm4.Gcm.streamEncryptPost PPC64LE.abi.ptrBits)) true
    (0 + 3296)).pre s := by
  implies_sat [Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamEncryptPost, PPC64LE.abi, PPC64LE.argRegs]
    [streamEncryptInnerSat, streamCryptSat] using streamEncryptInnerSat

def streamEncryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamCryptSig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamEncryptPost PPC64LE.abi.ptrBits)
    (writeArgs := true) (stack := 5888)).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamEncryptPost, PPC64LE.abi, PPC64LE.argRegs] [streamEncryptFrameSat, streamCryptSat] using streamEncryptFrameSat

theorem streamEncrypt_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 streamEncrypt))
      (Spec.Sm4.Gcm.streamCryptSig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamEncryptPost PPC64LE.abi.ptrBits) (writeArgs := true) (stack := 5888)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.streamEncryptPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 3296) (bytes := 2592)
    (PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig.withScratch "scratch" .u64 320) (nm := "sm4")
      (e := .u64) (n := 408) (wa := true) (stack := 0) (bytes := 3296) streamEncrypt_verified (by decide) (by decide)
      (pre_withScratch "scratch" .u64 320 (Proof.Sm4Gcm.pre_local _ _))
      (post_withScratch "scratch" .u64 320 (Proof.Sm4Gcm.streamEncryptPost_local _)) streamEncryptInnerSat_pre)
    (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.streamEncryptPost_local _) streamEncryptFrameSat_pre

/-! ## `stream_decrypt` -/

def streamDecryptInnerSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩] }

theorem streamDecryptInnerSat_pre : ∃ s, ((Spec.Sm4.Gcm.streamCryptSig.withScratch "scratch" .u64 320).contract PPC64LE.abi
    (Curry.withScratch PPC64LE.abi.ptrBits "scratch" .u64 320 Spec.Sm4.Gcm.streamCryptSig.params (Curry.const (fun _ => True) _))
    (Curry.withScratch PPC64LE.abi.ptrBits "scratch" .u64 320 Spec.Sm4.Gcm.streamCryptSig.params (Spec.Sm4.Gcm.streamDecryptPost PPC64LE.abi.ptrBits)) true
    (0 + 3296)).pre s := by
  implies_sat [Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamDecryptPost, PPC64LE.abi, PPC64LE.argRegs]
    [streamDecryptInnerSat, streamCryptSat] using streamDecryptInnerSat

def streamDecryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamCryptSig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamDecryptPost PPC64LE.abi.ptrBits)
    (writeArgs := true) (stack := 5888)).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamDecryptPost, PPC64LE.abi, PPC64LE.argRegs] [streamDecryptFrameSat, streamCryptSat] using streamDecryptFrameSat

theorem streamDecrypt_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 streamDecrypt))
      (Spec.Sm4.Gcm.streamCryptSig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamDecryptPost PPC64LE.abi.ptrBits) (writeArgs := true) (stack := 5888)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.streamDecryptPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 3296) (bytes := 2592)
    (PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig.withScratch "scratch" .u64 320) (nm := "sm4")
      (e := .u64) (n := 408) (wa := true) (stack := 0) (bytes := 3296) streamDecrypt_verified (by decide) (by decide)
      (pre_withScratch "scratch" .u64 320 (Proof.Sm4Gcm.pre_local _ _))
      (post_withScratch "scratch" .u64 320 (Proof.Sm4Gcm.streamDecryptPost_local _)) streamDecryptInnerSat_pre)
    (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.streamDecryptPost_local _) streamDecryptFrameSat_pre

/-! ## `stream_finish` -/

def streamFinishInnerSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩] }

theorem streamFinishInnerSat_pre : ∃ s, ((Spec.Sm4.Gcm.streamFinishSig.withScratch "work" .u64 320).contract PPC64LE.abi
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.streamFinishSig.params (Curry.const (fun _ => True) _))
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.streamFinishSig.params (Spec.Sm4.Gcm.streamFinishPost PPC64LE.abi.ptrBits)) true
    (0 + 3296)).pre s := by
  implies_sat [Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost, PPC64LE.abi, PPC64LE.argRegs]
    [streamFinishInnerSat, finSat] using streamFinishInnerSat

def streamFinishFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem streamFinishFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamFinishSig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamFinishPost PPC64LE.abi.ptrBits)
    (writeArgs := true) (stack := 5888)).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost, PPC64LE.abi, PPC64LE.argRegs] [streamFinishFrameSat, finSat] using streamFinishFrameSat

theorem streamFinish_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r8
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r9 streamFinish))
      (Spec.Sm4.Gcm.streamFinishSig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamFinishPost PPC64LE.abi.ptrBits) (writeArgs := true) (stack := 5888)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamFinishSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.streamFinishPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 3296) (bytes := 2592)
    (PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamFinishSig.withScratch "work" .u64 320) (nm := "sm4")
      (e := .u64) (n := 408) (wa := true) (stack := 0) (bytes := 3296) streamFinish_verified (by decide) (by decide)
      (pre_withScratch "work" .u64 320 (Proof.Sm4Gcm.pre_local _ _))
      (post_withScratch "work" .u64 320 (Proof.Sm4Gcm.streamFinishPost_local _)) streamFinishInnerSat_pre)
    (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.streamFinishPost_local _) streamFinishFrameSat_pre

/-! ## `stream_verify` -/

def streamVerifyInnerSat : State := { verSat with wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩] }

theorem streamVerifyInnerSat_pre : ∃ s, ((Spec.Sm4.Gcm.streamVerifySig.withScratch "work" .u64 320).contract PPC64LE.abi
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.streamVerifySig.params (Curry.const (fun _ => True) _))
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.streamVerifySig.params (Spec.Sm4.Gcm.streamVerifyPost PPC64LE.abi.ptrBits)) true
    (0 + 3296)).pre s := by
  implies_sat [Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost, PPC64LE.abi, PPC64LE.argRegs]
    [streamVerifyInnerSat, verSat] using streamVerifyInnerSat

def streamVerifyFrameSat : State := { verSat with wr := [⟨0x3000, 80⟩] }

theorem streamVerifyFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamVerifySig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamVerifyPost PPC64LE.abi.ptrBits)
    (writeArgs := true) (stack := 5888)).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost, PPC64LE.abi, PPC64LE.argRegs] [streamVerifyFrameSat, verSat] using streamVerifyFrameSat

theorem streamVerify_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 streamVerify))
      (Spec.Sm4.Gcm.streamVerifySig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamVerifyPost PPC64LE.abi.ptrBits) (writeArgs := true) (stack := 5888)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamVerifySig) (nm := "work") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.streamVerifyPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 3296) (bytes := 2592)
    (PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamVerifySig.withScratch "work" .u64 320) (nm := "sm4")
      (e := .u64) (n := 408) (wa := true) (stack := 0) (bytes := 3296) streamVerify_verified (by decide) (by decide)
      (pre_withScratch "work" .u64 320 (Proof.Sm4Gcm.pre_local _ _))
      (post_withScratch "work" .u64 320 (Proof.Sm4Gcm.streamVerifyPost_local _)) streamVerifyInnerSat_pre)
    (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.streamVerifyPost_local _) streamVerifyFrameSat_pre

/-! ## `seal` -/

/-- `sealSat` with the working space alone on the stack. -/
def sealInnerSat : State := { sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9060, 8⟩]
  wr := [⟨0x2800, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 2560⟩] }

theorem sealInnerSat_pre : ∃ s, ((Spec.Sm4.Gcm.sealSig.withScratch "work" .u64 320).contract PPC64LE.abi
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.sealSig.params
      (Curry.const (fun _ => True) _))
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.sealSig.params
      (Spec.Sm4.Gcm.sealPost PPC64LE.abi.ptrBits)) true (0 + 3376)).pre s := by
  implies_sat [Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost,
    PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealInnerSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealInnerSat

/-- `sealSat` without the stack arguments. -/
def sealFrameSat : State := { sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2800, 0⟩, ⟨0x5000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.sealContract PPC64LE.abi 6048).pre s := by
  implies_sat [Spec.Sm4.Gcm.sealContract, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost, PPC64LE.abi,
    PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

/-- `seal`: the outer frame passes the working space's address as the first
stack argument, and the inner frame copies it, then SM4's working space's
address, above its stack pointer (`Verified.stackScratchArgs`). -/
theorem seal_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 0
      (Impl.StackScratch.PPC64LE.withStackScratchArgs 3376 1 «seal»))
      (Spec.Sm4.Gcm.sealContract PPC64LE.abi 6048) :=
  PPC64LE.Verified.stackScratchArgs (sig := Spec.Sm4.Gcm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.sealPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 3376) (bytes := 2672) (m := 0)
    (PPC64LE.Verified.stackScratchArgs (sig := Spec.Sm4.Gcm.sealSig.withScratch "work" .u64 320) (nm := "sm4")
      (e := .u64) (n := 408) (wa := true) (stack := 0) (bytes := 3376) (m := 1) seal_verified (by decide)
      (by decide) (pre_withScratch "work" .u64 320 (Proof.Sm4Gcm.pre_local _ _))
      (post_withScratch "work" .u64 320 (Proof.Sm4Gcm.sealPost_local _)) sealInnerSat_pre)
    (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.sealPost_local _) sealFrameSat_pre

/-! ## `open` -/

/-- `openSat` with `tag_len` and the working space on the stack. -/
def openInnerSat : State := { openSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9060, 16⟩]
  wr := [⟨0x2800, 0⟩, ⟨0x6000, 2560⟩] }

theorem openInnerSat_pre : ∃ s, ((Spec.Sm4.Gcm.openSig.withScratch "work" .u64 320).contract PPC64LE.abi
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.openSig.params
      (Curry.const (fun _ => True) _))
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.openSig.params
      (Spec.Sm4.Gcm.openPost PPC64LE.abi.ptrBits)) true (0 + 3392)
    ((some (Spec.Sm4.Gcm.openLeak PPC64LE.abi.ptrBits)).map
      (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.openSig.params))).pre s := by
  implies_sat [Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost,
    Spec.Sm4.Gcm.openLeak, PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range,
    List.range.loop] [openInnerSat, openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openInnerSat

/-- `openSat` with `tag_len` alone on the stack. -/
def openFrameSat : State := { openSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9060, 8⟩]
  wr := [⟨0x2800, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.openContract PPC64LE.abi 6064).pre s := by
  implies_sat [Spec.Sm4.Gcm.openContract, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak,
    PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openFrameSat, openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openFrameSat

/-- `open`, whose `tag_len` arrives on the stack before the working spaces. -/
theorem open_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 1
      (Impl.StackScratch.PPC64LE.withStackScratchArgs 3392 2 «open»))
      (Spec.Sm4.Gcm.openContract PPC64LE.abi 6064) :=
  PPC64LE.Verified.stackScratchArgs (sig := Spec.Sm4.Gcm.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.openPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 3392) (bytes := 2672) (m := 1)
    (leak := some (Spec.Sm4.Gcm.openLeak PPC64LE.abi.ptrBits))
    (PPC64LE.Verified.stackScratchArgs (sig := Spec.Sm4.Gcm.openSig.withScratch "work" .u64 320) (nm := "sm4")
      (e := .u64) (n := 408) (wa := true) (stack := 0) (bytes := 3392) (m := 2) open_verified (by decide)
      (by decide) (pre_withScratch "work" .u64 320 (Proof.Sm4Gcm.pre_local _ _))
      (post_withScratch "work" .u64 320 (Proof.Sm4Gcm.openPost_local _)) openInnerSat_pre
      (hleak := leakLocal_withScratch "work" .u64 320 (Proof.Sm4Gcm.openLeak_local _)))
    (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.openPost_local _) openFrameSat_pre
    (hleak := Proof.Sm4Gcm.openLeak_local _)

end VG.Proof.Sm4Gcm.PPC64LE
