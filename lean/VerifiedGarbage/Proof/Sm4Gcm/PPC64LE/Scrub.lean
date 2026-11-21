module

public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Frame
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Frame
import VerifiedGarbage.Proof.Sm4Gcm.Scratch
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit

/-!
# SM4-GCM on PPC64LE, without secret residue

Each function keeps its working space in two frames, one inside the other
(the GHASH space `W` and SM4's `X`; `vg_sm4_gcm_stream_init` and
`vg_sm4_gcm_stream_aad`, AES-GCM's functions, only `W`), which it does not
zero: the tail after it wipes the whole stack its frames use, its contract's
`stack`, and clears the volatile registers it may write
(`PPC64LE.Scrub.verifiedScrubbedAll`). Their postconditions read the memory on return
only within their buffers, by the target-independent lemmas the frames'
proofs use (`Proof/Sm4Gcm/Scratch.lean`, `Proof/AesGcm/Scratch.lean`).

The registrations take GHASH's law (`Proof.Gcm.PPC64LE.GhashLaw`) as an
instance, as the frames' proofs do, so that only the registration file
imports its proof and the algebra it needs.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.initContract PPC64LE.abi stack) (Spec.Sm4.Gcm.initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.initPostOut_local _)

theorem sealOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.sealContract PPC64LE.abi stack) (Spec.Sm4.Gcm.sealSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.sealPostOut_local _)

theorem openOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.openContract PPC64LE.abi stack) (Spec.Sm4.Gcm.openSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain (Proof.Sm4Gcm.openPostOut_local _)

theorem streamInitOut (stack : Nat) :
    PostOut (Spec.Gcm.streamInitContract PPC64LE.abi stack) (Spec.Gcm.streamInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesGcm.streamInitPostOut_local _)

theorem streamAadOut (stack : Nat) :
    PostOut (Spec.Gcm.streamAadContract PPC64LE.abi stack) (Spec.Gcm.streamAadSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesGcm.streamAadPostOut_local _)

theorem streamEncryptOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamCryptSig.contract PPC64LE.abi
        (post := Spec.Sm4.Gcm.streamEncryptPost PPC64LE.abi.ptrBits) (writeArgs := true) (stack := stack))
      (Spec.Sm4.Gcm.streamCryptSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamEncryptPostOut_local _)

theorem streamDecryptOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamCryptSig.contract PPC64LE.abi
        (post := Spec.Sm4.Gcm.streamDecryptPost PPC64LE.abi.ptrBits) (writeArgs := true) (stack := stack))
      (Spec.Sm4.Gcm.streamCryptSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamDecryptPostOut_local _)

theorem streamFinishOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamFinishSig.contract PPC64LE.abi
        (post := Spec.Sm4.Gcm.streamFinishPost PPC64LE.abi.ptrBits) (writeArgs := true) (stack := stack))
      (Spec.Sm4.Gcm.streamFinishSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamFinishPostOut_local _)

theorem streamVerifyOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamVerifySig.contract PPC64LE.abi
        (post := Spec.Sm4.Gcm.streamVerifyPost PPC64LE.abi.ptrBits) (writeArgs := true) (stack := stack))
      (Spec.Sm4.Gcm.streamVerifySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamVerifyPostOut_local _)

/-! ## The functions as emitted -/

variable [VG.Proof.Gcm.PPC64LE.GhashLaw]

/-- The volatile registers the functions but `vg_sm4_gcm_init` may write:
every one but CA. -/
def allBut : Impl.Scrub.PPC64LE.Clear :=
  ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
     .v17, .v18, .v19]⟩

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] in
/-- `vg_sm4_gcm_init` as emitted (`Impl.Sm4Gcm.PPC64LE.Fn.init`) meets its
contract in constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm4Gcm.PPC64LE.Fn.init
      (Spec.Sm4.Gcm.initContract PPC64LE.abi 3616) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.initApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r5
        (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r6 Impl.Sm4Gcm.PPC64LE.init)
      verified := init_framed }
    3616 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩
    (initOut _) (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] in
/-- `vg_sm4_gcm_seal` as emitted (`Impl.Sm4Gcm.PPC64LE.Fn.seal`) meets its
contract in constant time and returns without secret residue. -/
theorem seal_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] :
    VerifiedScrubbed PPC64LE.target Impl.Sm4Gcm.PPC64LE.Fn.seal
      (Spec.Sm4.Gcm.sealContract PPC64LE.abi 3776) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.sealApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchArgs 400 0
        (Impl.StackScratch.PPC64LE.withStackScratchArgs 3376 1 Impl.Sm4Gcm.PPC64LE.«seal»)
      verified := seal_framed }
    3776 allBut (sealOut _) (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] in
/-- `vg_sm4_gcm_open` as emitted (`Impl.Sm4Gcm.PPC64LE.Fn.open`) meets its
contract in constant time and returns without secret residue. -/
theorem open_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] :
    VerifiedScrubbed PPC64LE.target Impl.Sm4Gcm.PPC64LE.Fn.open
      (Spec.Sm4.Gcm.openContract PPC64LE.abi 3792) 32 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.openApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchArgs 400 1
        (Impl.StackScratch.PPC64LE.withStackScratchArgs 3392 2 Impl.Sm4Gcm.PPC64LE.«open»)
      verified := open_framed }
    3792 allBut (openOut _) (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] in
/-- `vg_sm4_gcm_stream_init` as emitted (`Impl.Sm4Gcm.PPC64LE.Fn.streamInit`)
meets its contract in constant time and returns without secret residue. -/
theorem streamInit_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] :
    VerifiedScrubbed PPC64LE.target Impl.Sm4Gcm.PPC64LE.Fn.streamInit
      (Spec.Gcm.streamInitContract PPC64LE.abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.streamInitApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r7 Impl.AesGcm.PPC64LE.streamInit
      verified := Proof.AesGcm.PPC64LE.streamInit_framed }
    320 allBut (streamInitOut _) (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] in
/-- `vg_sm4_gcm_stream_aad` as emitted (`Impl.Sm4Gcm.PPC64LE.Fn.streamAad`) meets
its contract in constant time and returns without secret residue. -/
theorem streamAad_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] :
    VerifiedScrubbed PPC64LE.target Impl.Sm4Gcm.PPC64LE.Fn.streamAad
      (Spec.Gcm.streamAadContract PPC64LE.abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.streamAadApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r8 Impl.AesGcm.PPC64LE.streamAad
      verified := Proof.AesGcm.PPC64LE.streamAad_framed }
    320 allBut (streamAadOut _) (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] in
/-- `vg_sm4_gcm_stream_encrypt` as emitted
(`Impl.Sm4Gcm.PPC64LE.Fn.streamEncrypt`) meets its contract in constant time
and returns without secret residue. -/
theorem streamEncrypt_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] :
    VerifiedScrubbed PPC64LE.target Impl.Sm4Gcm.PPC64LE.Fn.streamEncrypt
      (Sig.contract PPC64LE.abi Spec.Sm4.Gcm.streamCryptSig (Curry.const (fun _ => True) (Spec.Sm4.Gcm.streamCryptSig.words PPC64LE.abi.ptrBits)) (Spec.Sm4.Gcm.streamEncryptPost PPC64LE.abi.ptrBits) true 3616) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.streamEncryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r9
        (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 Impl.Sm4Gcm.PPC64LE.streamEncrypt)
      verified := streamEncrypt_framed }
    3616 allBut (streamEncryptOut _) (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] in
/-- `vg_sm4_gcm_stream_decrypt` as emitted
(`Impl.Sm4Gcm.PPC64LE.Fn.streamDecrypt`) meets its contract in constant time
and returns without secret residue. -/
theorem streamDecrypt_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] :
    VerifiedScrubbed PPC64LE.target Impl.Sm4Gcm.PPC64LE.Fn.streamDecrypt
      (Sig.contract PPC64LE.abi Spec.Sm4.Gcm.streamCryptSig (Curry.const (fun _ => True) (Spec.Sm4.Gcm.streamCryptSig.words PPC64LE.abi.ptrBits)) (Spec.Sm4.Gcm.streamDecryptPost PPC64LE.abi.ptrBits) true 3616) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.streamDecryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r9
        (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 Impl.Sm4Gcm.PPC64LE.streamDecrypt)
      verified := streamDecrypt_framed }
    3616 allBut (streamDecryptOut _) (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] in
/-- `vg_sm4_gcm_stream_finish` as emitted (`Impl.Sm4Gcm.PPC64LE.Fn.streamFinish`)
meets its contract in constant time and returns without secret residue. -/
theorem streamFinish_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] :
    VerifiedScrubbed PPC64LE.target Impl.Sm4Gcm.PPC64LE.Fn.streamFinish
      (Sig.contract PPC64LE.abi Spec.Sm4.Gcm.streamFinishSig (Curry.const (fun _ => True) (Spec.Sm4.Gcm.streamFinishSig.words PPC64LE.abi.ptrBits)) (Spec.Sm4.Gcm.streamFinishPost PPC64LE.abi.ptrBits) true 3616) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.streamFinishApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r8
        (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r9 Impl.Sm4Gcm.PPC64LE.streamFinish)
      verified := streamFinish_framed }
    3616 allBut (streamFinishOut _) (by dsimp only; lit_decide)

omit [VG.Proof.Gcm.PPC64LE.GhashLaw] in
/-- `vg_sm4_gcm_stream_verify` as emitted (`Impl.Sm4Gcm.PPC64LE.Fn.streamVerify`)
meets its contract in constant time and returns without secret residue. -/
theorem streamVerify_scrubbed [Proof.Gcm.PPC64LE.GhashLaw] :
    VerifiedScrubbed PPC64LE.target Impl.Sm4Gcm.PPC64LE.Fn.streamVerify
      (Sig.contract PPC64LE.abi Spec.Sm4.Gcm.streamVerifySig (Curry.const (fun _ => True) (Spec.Sm4.Gcm.streamVerifySig.words PPC64LE.abi.ptrBits)) (Spec.Sm4.Gcm.streamVerifyPost PPC64LE.abi.ptrBits) true 3616) 32 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.streamVerifyApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r9
        (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 Impl.Sm4Gcm.PPC64LE.streamVerify)
      verified := streamVerify_framed }
    3616 allBut (streamVerifyOut _) (by dsimp only; lit_decide)

end VG.Proof.Sm4Gcm.PPC64LE.Scrub
