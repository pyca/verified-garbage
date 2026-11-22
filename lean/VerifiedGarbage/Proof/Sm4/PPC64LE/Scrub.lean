module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.CfbFinal
public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Sm4.OfbFinal
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Spec.Sm4.CtrFinal
public import VerifiedGarbage.Proof.Sm4.PPC64LE.CtrVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.CtrFinal
public import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Verified
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Sm4.CbcScratch
import VerifiedGarbage.Proof.Sm4.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.Sm4.CtrFinal
import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM4 on PPC64LE, without secret residue

Key expansion and the ECB, CBC, CFB128, OFB and CTR functions zero their
whole frame themselves before they release it (`withStackScratchWiped`), and
have no frames of their own inside it, so they need only the clearing of the
volatile registers after them (`PPC64LE.Scrub.verifiedScrubbedWiped`), with no stack
wiped. Their postconditions read the memory on return only within their
buffers, by the target-independent lemmas RISC-V's and x86-64's proofs use
(`Proof/Sm4/RISCV64/Scrub.lean`).

`vg_sm4_ctr_final` runs `vg_sm4_ctr`'s code, as `vg_sm4_ctr_core`
(`Impl.Sm4.PPC64LE.ctrCall`), inside its own frame, so its body has a frame
inside the one it wipes: the tail after it wipes the whole stack both frames
use, the 3408 bytes of its contract's `stack`, and clears the volatile
registers (`PPC64LE.Scrub.verifiedScrubbedAll`).
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) : PostOut (Spec.Sm4.expandKeyContract PPC64LE.abi stack) (Spec.Sm4.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.expandKeyPostOut_local _)

theorem ecbEncryptOut (stack : Nat) : PostOut (Spec.Sm4.ecbContract PPC64LE.abi .encrypt stack) (Spec.Sm4.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ecbPostOut_local _ .encrypt)

theorem ecbDecryptOut (stack : Nat) : PostOut (Spec.Sm4.ecbContract PPC64LE.abi .decrypt stack) (Spec.Sm4.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ecbPostOut_local _ .decrypt)

theorem cbcEncryptOut (stack : Nat) : PostOut (Spec.Sm4.cbcEncryptChainedContract PPC64LE.abi stack) (Spec.Sm4.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cbcEncChainedPostOut_local _)

theorem cbcDecryptOut (stack : Nat) : PostOut (Spec.Sm4.cbcDecryptChainedContract PPC64LE.abi stack) (Spec.Sm4.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cbcDecChainedPostOut_local _)

theorem cfbEncryptOut (stack : Nat) : PostOut (Spec.Sm4.cfbEncryptContract PPC64LE.abi stack) (Spec.Sm4.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cfbEncPostOut_local _)

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (Spec.Sm4.cfbEncryptFinalContract PPC64LE.abi stack) (Spec.Sm4.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptOut (stack : Nat) : PostOut (Spec.Sm4.cfbDecryptContract PPC64LE.abi stack) (Spec.Sm4.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cfbDecPostOut_local _)

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (Spec.Sm4.cfbDecryptFinalContract PPC64LE.abi stack) (Spec.Sm4.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem ofbOut (stack : Nat) : PostOut (Spec.Sm4.ofbContract PPC64LE.abi stack) (Spec.Sm4.ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ofbPostOut_local _)

theorem ofbFinalOut (stack : Nat) : PostOut (Spec.Sm4.ofbFinalContract PPC64LE.abi stack) (Spec.Sm4.ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

theorem ctrOut (stack : Nat) : PostOut (Spec.Sm4.ctrContract PPC64LE.abi stack) (Spec.Sm4.ctrSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ctrPostOut_local _)

theorem ctrFinalOut (stack : Nat) : PostOut (Spec.Sm4.ctrFinalContract PPC64LE.abi stack) (Spec.Sm4.ctrFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ctrFinalPostOut_local _)

/-! ## The functions as emitted -/

/-- `vg_sm4_expand_key` as emitted (`Impl.Sm4.PPC64LE.Fn.expandKey`) meets its
contract in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm4.PPC64LE.Fn.expandKey
      (Spec.Sm4.expandKeyContract PPC64LE.abi 3264) 0 :=
  verifiedScrubbedWiped (api := Spec.Sm4.expandKeyApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3264 .r5 404 Impl.Sm4.PPC64LE.expandKeyCall
      verified := Proof.Sm4.PPC64LE.expandKey_framed }
    3264 .r5 404 Impl.Sm4.PPC64LE.expandKeyCall
    ⟨true, false, [.r4, .r5, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (expandKeyOut _) (by dsimp only; lit_decide)

/-- `vg_sm4_ecb_encrypt` as emitted (`Impl.Sm4.PPC64LE.Fn.ecbEncrypt`) meets its
contract in constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm4.PPC64LE.Fn.ecbEncrypt
      (Spec.Sm4.ecbContract PPC64LE.abi (Proof.Sm4.specDirPPC64LE Impl.Sm4.PPC64LE.Dir.encrypt) 3280) 0 :=
  verifiedScrubbedWiped (api := Spec.Sm4.ecbEncryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3280 .r6 406 (Impl.Sm4.PPC64LE.ecb .encrypt)
      verified := Proof.Sm4.PPC64LE.ecb_framed .encrypt }
    3280 .r6 406 (Impl.Sm4.PPC64LE.ecb .encrypt)
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (ecbEncryptOut _) (by dsimp only; lit_decide)

/-- `vg_sm4_ecb_decrypt` as emitted (`Impl.Sm4.PPC64LE.Fn.ecbDecrypt`) meets its
contract in constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm4.PPC64LE.Fn.ecbDecrypt
      (Spec.Sm4.ecbContract PPC64LE.abi (Proof.Sm4.specDirPPC64LE Impl.Sm4.PPC64LE.Dir.decrypt) 3280) 0 :=
  verifiedScrubbedWiped (api := Spec.Sm4.ecbDecryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3280 .r6 406 (Impl.Sm4.PPC64LE.ecb .decrypt)
      verified := Proof.Sm4.PPC64LE.ecb_framed .decrypt }
    3280 .r6 406 (Impl.Sm4.PPC64LE.ecb .decrypt)
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (ecbDecryptOut _) (by dsimp only; lit_decide)

/-- `vg_sm4_cbc_encrypt_chained` as emitted (`Impl.Sm4.PPC64LE.Fn.cbcEncrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem cbcEncrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm4.PPC64LE.Fn.cbcEncrypt
      (Spec.Sm4.cbcEncryptChainedContract PPC64LE.abi 3296) 0 :=
  verifiedScrubbedWiped (api := Spec.Sm4.cbcEncryptChainedApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cbcEncryptChained
      verified := Proof.Sm4.PPC64LE.cbcEnc_framed Proof.Sm4.PPC64LE.Modes.cbcEncryptChained_verified }
    3296 .r7 408 Impl.Sm4.PPC64LE.cbcEncryptChained
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (cbcEncryptOut _) (by dsimp only; lit_decide)

/-- `vg_sm4_cbc_decrypt_chained` as emitted (`Impl.Sm4.PPC64LE.Fn.cbcDecrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem cbcDecrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm4.PPC64LE.Fn.cbcDecrypt
      (Spec.Sm4.cbcDecryptChainedContract PPC64LE.abi 3296) 0 :=
  verifiedScrubbedWiped (api := Spec.Sm4.cbcDecryptChainedApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cbcDecryptChained
      verified := Proof.Sm4.PPC64LE.cbcDec_framed Proof.Sm4.PPC64LE.Modes.cbcDecryptChained_verified }
    3296 .r7 408 Impl.Sm4.PPC64LE.cbcDecryptChained
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (cbcDecryptOut _) (by dsimp only; lit_decide)

/-- `vg_sm4_cfb128_encrypt` as emitted (`Impl.Sm4.PPC64LE.Fn.cfbEncrypt`) meets
its contract in constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm4.PPC64LE.Fn.cfbEncrypt
      (Spec.Sm4.cfbEncryptContract PPC64LE.abi 3296) 0 :=
  verifiedScrubbedWiped (api := Spec.Sm4.cfbEncryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cfbEncrypt
      verified := Proof.Sm4.PPC64LE.cfbEnc_framed Proof.Sm4.PPC64LE.Modes.cfbEncrypt_verified }
    3296 .r7 408 Impl.Sm4.PPC64LE.cfbEncrypt
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (cfbEncryptOut _) (by dsimp only; lit_decide)

/-- `vg_sm4_cfb128_decrypt` as emitted (`Impl.Sm4.PPC64LE.Fn.cfbDecrypt`) meets
its contract in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm4.PPC64LE.Fn.cfbDecrypt
      (Spec.Sm4.cfbDecryptContract PPC64LE.abi 3296) 0 :=
  verifiedScrubbedWiped (api := Spec.Sm4.cfbDecryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cfbDecrypt
      verified := Proof.Sm4.PPC64LE.cfbDec_framed Proof.Sm4.PPC64LE.Modes.cfbDecrypt_verified }
    3296 .r7 408 Impl.Sm4.PPC64LE.cfbDecrypt
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (cfbDecryptOut _) (by dsimp only; lit_decide)

/-- `vg_sm4_cfb128_encrypt_final` as emitted
(`Impl.Sm4.PPC64LE.Fn.cfbEncryptFinal`) meets its contract in constant time
and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm4.PPC64LE.Fn.cfbEncryptFinal
      (Spec.Sm4.cfbEncryptFinalContract PPC64LE.abi 3296) 0 :=
  verifiedScrubbedWiped (api := Spec.Sm4.cfbEncryptFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cfbEncryptFinal
      verified := Proof.Sm4.PPC64LE.FbFinal.cfbEncryptFinal_framed }
    3296 .r7 408 Impl.Sm4.PPC64LE.cfbEncryptFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (cfbEncryptFinalOut _) (by dsimp only; lit_decide)

/-- `vg_sm4_cfb128_decrypt_final` as emitted
(`Impl.Sm4.PPC64LE.Fn.cfbDecryptFinal`) meets its contract in constant time
and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm4.PPC64LE.Fn.cfbDecryptFinal
      (Spec.Sm4.cfbDecryptFinalContract PPC64LE.abi 3296) 0 :=
  verifiedScrubbedWiped (api := Spec.Sm4.cfbDecryptFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cfbDecryptFinal
      verified := Proof.Sm4.PPC64LE.FbFinal.cfbDecryptFinal_framed }
    3296 .r7 408 Impl.Sm4.PPC64LE.cfbDecryptFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (cfbDecryptFinalOut _) (by dsimp only; lit_decide)

/-- `vg_sm4_ofb` as emitted (`Impl.Sm4.PPC64LE.Fn.ofb`) meets its contract in
constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm4.PPC64LE.Fn.ofb
      (Spec.Sm4.ofbContract PPC64LE.abi 3296) 0 :=
  verifiedScrubbedWiped (api := Spec.Sm4.ofbApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.ofb
      verified := Proof.Sm4.PPC64LE.ofb_framed Proof.Sm4.PPC64LE.Modes.ofb_verified }
    3296 .r7 408 Impl.Sm4.PPC64LE.ofb
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (ofbOut _) (by dsimp only; lit_decide)

/-- `vg_sm4_ofb_final` as emitted (`Impl.Sm4.PPC64LE.Fn.ofbFinal`) meets its
contract in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm4.PPC64LE.Fn.ofbFinal
      (Spec.Sm4.ofbFinalContract PPC64LE.abi 3296) 0 :=
  verifiedScrubbedWiped (api := Spec.Sm4.ofbFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.ofbFinal
      verified := Proof.Sm4.PPC64LE.FbFinal.ofbFinal_framed }
    3296 .r7 408 Impl.Sm4.PPC64LE.ofbFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (ofbFinalOut _) (by dsimp only; lit_decide)

/-- `vg_sm4_ctr` as emitted (`Impl.Sm4.PPC64LE.Fn.ctr`) meets its contract in
constant time and returns without secret residue. -/
theorem ctr_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm4.PPC64LE.Fn.ctr
      (Spec.Sm4.ctrContract PPC64LE.abi 3296) 0 :=
  verifiedScrubbedWiped (api := Spec.Sm4.ctrApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.ctr
      verified := Proof.Sm4.PPC64LE.Modes.ctr_framed }
    3296 .r7 408 Impl.Sm4.PPC64LE.ctr
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (ctrOut _) (by dsimp only; lit_decide)

/-- `vg_sm4_ctr_final` as emitted (`Impl.Sm4.PPC64LE.Fn.ctrFinal`) meets its
contract in constant time and returns without secret residue. -/
theorem ctrFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm4.PPC64LE.Fn.ctrFinal
      (Spec.Sm4.ctrFinalContract PPC64LE.abi 3408) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.ctrFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 112 .r7 10 Impl.Sm4.PPC64LE.ctrFinal
      verified := Proof.Sm4.PPC64LE.CtrFinal.ctrFinal_framed }
    3408 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩
    (ctrFinalOut _) (by dsimp only; lit_decide)

end VG.Proof.Sm4.PPC64LE.Scrub
