module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Verified
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
import VerifiedGarbage.Proof.Sm4Gcm.Scratch
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Verified
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
meta import VerifiedGarbage.Proof.Sm4Gcm.Scratch
meta import VerifiedGarbage.Proof.AesGcm.Scratch
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
meta import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Lit

/-!
# SM4-GCM on RISC-V, without secret residue

Each function keeps its working space `W` (2560 bytes) in a frame below the
stack pointer, and `vg_sm4_ctr32`, `vg_sm4_expand_key_core` and `vg_ghash`
keep theirs in frames of their own below it, none of which it zeroes. The
residue analysis (`RISCV64.rtaint`) finds every byte of that stack may hold
a secret: the byte loops that copy the caller's buffers store through
pointers it cannot place, which makes every frame then allocated secret, `W`
among them, and the callees' frames hold the keystream, the GHASH table and
the key schedule's working space. So the tail after the code wipes the whole
stack its frames use, its contract's `stack`, and clears the caller-saved
registers (`RISCV64.Scrub.scrubOf`).

`vg_sm4_gcm_stream_init` and `vg_sm4_gcm_stream_aad`, AES-GCM's functions,
call only `vg_ghash`, whose table does not reach the bottom 400 bytes of
their 4608: the tail clears only the 526 doublewords above them
(`RISCV64.Scrub.scrubSelOf`, `scrubSel_noResidue`).

Their postconditions read the memory on return only within their buffers, by
the target-independent lemmas the frames' proofs use
(`Proof/Sm4Gcm/Scratch.lean`, `Proof/AesGcm/Scratch.lean`). The
registrations take GHASH's law (`Proof.Gcm.RISCV64.GhashLaw`) as an
instance, as the frames' proofs do.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.initContract RISCV64.abi stack) (Spec.Sm4.Gcm.initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.initPostOut_local _)

theorem sealOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.sealContract RISCV64.abi stack) (Spec.Sm4.Gcm.sealSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.sealPostOut_local _)

theorem openOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.openContract RISCV64.abi stack) (Spec.Sm4.Gcm.openSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain (Proof.Sm4Gcm.openPostOut_local _)

theorem streamInitOut (stack : Nat) :
    PostOut (Spec.Gcm.streamInitContract RISCV64.abi stack) (Spec.Gcm.streamInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesGcm.streamInitPostOut_local _)

theorem streamAadOut (stack : Nat) :
    PostOut (Spec.Gcm.streamAadContract RISCV64.abi stack) (Spec.Gcm.streamAadSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesGcm.streamAadPostOut_local _)

theorem streamEncryptOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamCryptSig.contract RISCV64.abi
        (post := Spec.Sm4.Gcm.streamEncryptPost RISCV64.abi.ptrBits) (writeArgs := true) (stack := stack))
      (Spec.Sm4.Gcm.streamCryptSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamEncryptPostOut_local _)

theorem streamDecryptOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamCryptSig.contract RISCV64.abi
        (post := Spec.Sm4.Gcm.streamDecryptPost RISCV64.abi.ptrBits) (writeArgs := true) (stack := stack))
      (Spec.Sm4.Gcm.streamCryptSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamDecryptPostOut_local _)

theorem streamFinishOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamFinishSig.contract RISCV64.abi
        (post := Spec.Sm4.Gcm.streamFinishPost RISCV64.abi.ptrBits) (writeArgs := true) (stack := stack))
      (Spec.Sm4.Gcm.streamFinishSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamFinishPostOut_local _)

theorem streamVerifyOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamVerifySig.contract RISCV64.abi
        (post := Spec.Sm4.Gcm.streamVerifyPost RISCV64.abi.ptrBits) (writeArgs := true) (stack := stack))
      (Spec.Sm4.Gcm.streamVerifySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamVerifyPostOut_local _)

/-! ## The registrations -/

variable [VG.Proof.Gcm.RISCV64.GhashLaw]

/-- `Spec.Sm4.Gcm.initApi`. -/
def initReg : Registration Spec.Sm4.Gcm.initApi RISCV64.target :=
  scrubOf {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a2 Impl.Sm4Gcm.RISCV64.init
      verified := init_framed }
    (initOut _)

/-- `Spec.Sm4.Gcm.sealApi`. -/
def sealReg : Registration Spec.Sm4.Gcm.sealApi RISCV64.target :=
  scrubOf {
      code := Impl.StackScratch.RISCV64.withStackScratchArgs 2576 0 Impl.Sm4Gcm.RISCV64.«seal»
      verified := seal_framed }
    (sealOut _)

/-- `Spec.Sm4.Gcm.openApi`. -/
def openReg : Registration Spec.Sm4.Gcm.openApi RISCV64.target :=
  scrubOf {
      code := Impl.StackScratch.RISCV64.withStackScratchArgs 2576 1 Impl.Sm4Gcm.RISCV64.«open»
      verified := open_framed }
    (openOut _)

/-- The runs `stream_init` and `stream_aad` clear: the top 4208 bytes of their
4608, in nested frames of 2048, 2048 and 112 bytes. -/
def ghashRuns : List (Nat × List (Nat × Nat)) := [(2048, [(0, 256)]), (2048, [(0, 256)]), (112, [(0, 14)])]

/-- `Spec.Sm4.Gcm.streamInitApi`. -/
def streamInitReg : Registration Spec.Sm4.Gcm.streamInitApi RISCV64.target :=
  scrubSelOf {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a4 Impl.AesGcm.RISCV64.streamInit
      verified := Proof.AesGcm.RISCV64.streamInit_framed }
    ghashRuns (streamInitOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (streamInitOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratch 2560 .a4 Impl.AesGcm.RISCV64.streamInit) 4608 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.Sm4.Gcm.streamAadApi`. -/
def streamAadReg : Registration Spec.Sm4.Gcm.streamAadApi RISCV64.target :=
  scrubSelOf {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a5 Impl.AesGcm.RISCV64.streamAad
      verified := Proof.AesGcm.RISCV64.streamAad_framed }
    ghashRuns (streamAadOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (streamAadOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratch 2560 .a5 Impl.AesGcm.RISCV64.streamAad) 4608 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.Sm4.Gcm.streamEncryptApi`. -/
def streamEncryptReg : Registration Spec.Sm4.Gcm.streamEncryptApi RISCV64.target :=
  scrubOf {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 Impl.Sm4Gcm.RISCV64.streamEncrypt
      verified := streamEncrypt_framed }
    (streamEncryptOut _)

/-- `Spec.Sm4.Gcm.streamDecryptApi`. -/
def streamDecryptReg : Registration Spec.Sm4.Gcm.streamDecryptApi RISCV64.target :=
  scrubOf {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 Impl.Sm4Gcm.RISCV64.streamDecrypt
      verified := streamDecrypt_framed }
    (streamDecryptOut _)

/-- `Spec.Sm4.Gcm.streamFinishApi`. -/
def streamFinishReg : Registration Spec.Sm4.Gcm.streamFinishApi RISCV64.target :=
  scrubOf {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a5 Impl.Sm4Gcm.RISCV64.streamFinish
      verified := streamFinish_framed }
    (streamFinishOut _)

/-- `Spec.Sm4.Gcm.streamVerifyApi`. -/
def streamVerifyReg : Registration Spec.Sm4.Gcm.streamVerifyApi RISCV64.target :=
  scrubOf {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 Impl.Sm4Gcm.RISCV64.streamVerify
      verified := streamVerify_framed }
    (streamVerifyOut _)

end VG.Proof.Sm4Gcm.RISCV64.Scrub
