module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Verified
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs
import VerifiedGarbage.Proof.Framework.SigEval

/-!
# AES-GCM on PPC64LE, with its working space on the stack

Each function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame of 2592 bytes that allocates it
(`Verified.stackScratch`): its arguments all arrive in registers, the
working space in the next one.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    PPC64LE.abi, PPC64LE.argRegs] [initFrameSat] using initFrameSat

theorem init_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r6 init)
      (Spec.Gcm.initContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre PPC64LE.abi.ptrBits) (post := Spec.Gcm.initPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2592) init_verified (by decide) (by decide)
    (Proof.AesGcm.initPre_local _) (Proof.AesGcm.initPost_local _) initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩]

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    PPC64LE.abi, PPC64LE.argRegs] [streamInitFrameSat] using streamInitFrameSat

theorem streamInit_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r7 streamInit)
      (Spec.Gcm.streamInitContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamInit_verified (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.AesGcm.streamInitPost_local _)
    streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r6 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩]

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    PPC64LE.abi, PPC64LE.argRegs] [streamAadFrameSat] using streamAadFrameSat

theorem streamAad_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r8 streamAad)
      (Spec.Gcm.streamAadContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamAad_verified (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.AesGcm.streamAadPost_local _)
    streamAadFrameSat_pre

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt` and
`vg_aes_gcm_stream_decrypt`, without the working space. -/
def streamCryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Gcm.streamEncryptContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamEncryptPost, PPC64LE.abi, PPC64LE.argRegs] [streamCryptFrameSat, streamCryptSat]
    using streamCryptFrameSat

theorem streamEncrypt_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r10 streamEncrypt)
      (Spec.Gcm.streamEncryptContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre PPC64LE.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamEncrypt_verified (by decide) (by decide)
    (Proof.AesGcm.streamTextPre_local _) (Proof.AesGcm.streamEncryptPost_local _) streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Gcm.streamDecryptContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamDecryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamDecryptPost, PPC64LE.abi, PPC64LE.argRegs] [streamCryptFrameSat, streamCryptSat]
    using streamCryptFrameSat

theorem streamDecrypt_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r10 streamDecrypt)
      (Spec.Gcm.streamDecryptContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre PPC64LE.abi.ptrBits)
    (post := Spec.Gcm.streamDecryptPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamDecrypt_verified (by decide) (by decide)
    (Proof.AesGcm.streamTextPre_local _) (Proof.AesGcm.streamDecryptPost_local _) streamDecryptFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition, without
the working space. -/
def finFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Gcm.streamFinishContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Spec.Gcm.streamFinishPost, PPC64LE.abi, PPC64LE.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9 streamFinish)
      (Spec.Gcm.streamFinishContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamFinishPre PPC64LE.abi.ptrBits)
    (post := Spec.Gcm.streamFinishPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamFinish_verified (by decide) (by decide)
    (Proof.AesGcm.streamFinishPre_local _) (Proof.AesGcm.streamFinishPost_local _) finFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition, without
the working space. -/
def verFrameSat : State := { verSat with wr := [⟨0x3000, 80⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Gcm.streamVerifyContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Spec.Gcm.streamVerifyPost, PPC64LE.abi, PPC64LE.argRegs] [verFrameSat, verSat] using verFrameSat

theorem streamVerify_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r10 streamVerify)
      (Spec.Gcm.streamVerifyContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamVerifyPre PPC64LE.abi.ptrBits)
    (post := Spec.Gcm.streamVerifyPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamVerify_verified (by decide) (by decide)
    (Proof.AesGcm.streamVerifyPre_local _) (Proof.AesGcm.streamVerifyPost_local _) verFrameSat_pre

/-- A state satisfying `vg_aes_gcm_seal`'s precondition, without the working
space: `tag` alone on the stack. -/
def sealFrameSat : State where
  gpr := sealSat.gpr
  lr := 0
  sp := 0x9000
  mem := sealSat.mem
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9060, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩]

theorem sealFrameSat_pre : ∃ s, (Spec.Gcm.sealContract PPC64LE.abi 2672).pre s := by
  implies_sat [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Spec.Gcm.sealPost, PPC64LE.abi,
    PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

/-- `seal`, whose `tag` arrives on the stack: the frame copies it, then the
working space's address, above its stack pointer (`Verified.stackScratchArgs`). -/
theorem seal_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 1 Impl.AesGcm.PPC64LE.SealFused.seal)
      (Spec.Gcm.sealContract PPC64LE.abi 2672) :=
  PPC64LE.Verified.stackScratchArgs (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.sealPre PPC64LE.abi.ptrBits) (post := Spec.Gcm.sealPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2672) (m := 1) sealFused_verified (by decide) (by decide)
    (Proof.AesGcm.sealPre_local _) (Proof.AesGcm.sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_open`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def openFrameSat : State where
  gpr := openSat.gpr
  lr := 0
  sp := 0x9000
  mem := openSat.mem
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9060, 16⟩]
  wr := [⟨0x4000, 0⟩]

theorem openFrameSat_pre : ∃ s, (Spec.Gcm.openContract PPC64LE.abi 2688).pre s := by
  implies_sat [Spec.Gcm.openContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Spec.Gcm.openPost, Spec.Gcm.openLeak,
    PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openFrameSat, openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openFrameSat

/-- `open`, whose `tag` and `tag_len` arrive on the stack, as `seal`'s `tag` does. -/
theorem open_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 «open»)
      (Spec.Gcm.openContract PPC64LE.abi 2688) :=
  PPC64LE.Verified.stackScratchArgs (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.openPre PPC64LE.abi.ptrBits) (post := Spec.Gcm.openPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2688) (m := 2) (leak := some (Spec.Gcm.openLeak PPC64LE.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.AesGcm.openPre_local _) (Proof.AesGcm.openPost_local _)
    openFrameSat_pre (hleak := Proof.AesGcm.openLeak_local _)

end VG.Proof.AesGcm.PPC64LE
