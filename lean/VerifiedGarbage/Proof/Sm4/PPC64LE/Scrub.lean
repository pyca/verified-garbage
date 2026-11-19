module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.CfbFinal
public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Sm4.OfbFinal
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Proof.Sm4.PPC64LE.CtrVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Verified
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Sm4.CbcScratch
import VerifiedGarbage.Proof.Sm4.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM4 on PPC64LE, without secret residue

Key expansion and the ECB, CBC, CFB128, OFB and CTR functions zero their
whole frame themselves before they release it (`withStackScratchWiped`), and
have no frames of their own inside it, so they need only the clearing of the
volatile registers after them (`PPC64LE.Scrub.scrubWipedOf`), with no stack
wiped. Their postconditions read the memory on return only within their
buffers, by the target-independent lemmas RISC-V's and x86-64's proofs use
(`Proof/Sm4/RISCV64/Scrub.lean`).

`vg_sm4_ctr_final` is not here: it runs `vg_sm4_ctr`'s frame inside its own,
and calls its code as `vg_sm4_ctr_core` (`Impl.Sm4.PPC64LE.ctrCall`).
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

/-! ## The registrations -/

/-- `Spec.Sm4.expandKeyApi`. -/
def expandKeyReg : Registration Spec.Sm4.expandKeyApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3248 .r5 402 Impl.Sm4.PPC64LE.expandKey
      verified := Proof.Sm4.PPC64LE.expandKey_framed }
    3248 .r5 402 Impl.Sm4.PPC64LE.expandKey
    ⟨true, false, [.r4, .r5, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (expandKeyOut _) (by dsimp only; lit_decide)

/-- `Spec.Sm4.ecbEncryptApi`. -/
def ecbEncryptReg : Registration Spec.Sm4.ecbEncryptApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3248 .r6 402 (Impl.Sm4.PPC64LE.ecb .encrypt)
      verified := Proof.Sm4.PPC64LE.ecb_framed .encrypt }
    3248 .r6 402 (Impl.Sm4.PPC64LE.ecb .encrypt)
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (ecbEncryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Sm4.ecbDecryptApi`. -/
def ecbDecryptReg : Registration Spec.Sm4.ecbDecryptApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3248 .r6 402 (Impl.Sm4.PPC64LE.ecb .decrypt)
      verified := Proof.Sm4.PPC64LE.ecb_framed .decrypt }
    3248 .r6 402 (Impl.Sm4.PPC64LE.ecb .decrypt)
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (ecbDecryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Sm4.cbcEncryptChainedApi`. -/
def cbcEncryptReg : Registration Spec.Sm4.cbcEncryptChainedApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cbcEncryptChained
      verified := Proof.Sm4.PPC64LE.cbcEnc_framed Proof.Sm4.PPC64LE.Modes.cbcEncryptChained_verified }
    3296 .r7 408 Impl.Sm4.PPC64LE.cbcEncryptChained
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (cbcEncryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Sm4.cbcDecryptChainedApi`. -/
def cbcDecryptReg : Registration Spec.Sm4.cbcDecryptChainedApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cbcDecryptChained
      verified := Proof.Sm4.PPC64LE.cbcDec_framed Proof.Sm4.PPC64LE.Modes.cbcDecryptChained_verified }
    3296 .r7 408 Impl.Sm4.PPC64LE.cbcDecryptChained
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (cbcDecryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Sm4.cfbEncryptApi`. -/
def cfbEncryptReg : Registration Spec.Sm4.cfbEncryptApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cfbEncrypt
      verified := Proof.Sm4.PPC64LE.cfbEnc_framed Proof.Sm4.PPC64LE.Modes.cfbEncrypt_verified }
    3296 .r7 408 Impl.Sm4.PPC64LE.cfbEncrypt
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (cfbEncryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Sm4.cfbDecryptApi`. -/
def cfbDecryptReg : Registration Spec.Sm4.cfbDecryptApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cfbDecrypt
      verified := Proof.Sm4.PPC64LE.cfbDec_framed Proof.Sm4.PPC64LE.Modes.cfbDecrypt_verified }
    3296 .r7 408 Impl.Sm4.PPC64LE.cfbDecrypt
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (cfbDecryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Sm4.cfbEncryptFinalApi`. -/
def cfbEncryptFinalReg : Registration Spec.Sm4.cfbEncryptFinalApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cfbEncryptFinal
      verified := Proof.Sm4.PPC64LE.FbFinal.cfbEncryptFinal_framed }
    3296 .r7 408 Impl.Sm4.PPC64LE.cfbEncryptFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (cfbEncryptFinalOut _) (by dsimp only; lit_decide)

/-- `Spec.Sm4.cfbDecryptFinalApi`. -/
def cfbDecryptFinalReg : Registration Spec.Sm4.cfbDecryptFinalApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cfbDecryptFinal
      verified := Proof.Sm4.PPC64LE.FbFinal.cfbDecryptFinal_framed }
    3296 .r7 408 Impl.Sm4.PPC64LE.cfbDecryptFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (cfbDecryptFinalOut _) (by dsimp only; lit_decide)

/-- `Spec.Sm4.ofbApi`. -/
def ofbReg : Registration Spec.Sm4.ofbApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.ofb
      verified := Proof.Sm4.PPC64LE.ofb_framed Proof.Sm4.PPC64LE.Modes.ofb_verified }
    3296 .r7 408 Impl.Sm4.PPC64LE.ofb
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (ofbOut _) (by dsimp only; lit_decide)

/-- `Spec.Sm4.ofbFinalApi`. -/
def ofbFinalReg : Registration Spec.Sm4.ofbFinalApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.ofbFinal
      verified := Proof.Sm4.PPC64LE.FbFinal.ofbFinal_framed }
    3296 .r7 408 Impl.Sm4.PPC64LE.ofbFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (ofbFinalOut _) (by dsimp only; lit_decide)

/-- `Spec.Sm4.ctrApi`. -/
def ctrReg : Registration Spec.Sm4.ctrApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.ctr
      verified := Proof.Sm4.PPC64LE.Modes.ctr_framed }
    3296 .r7 408 Impl.Sm4.PPC64LE.ctr
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v12, .v13, .v14, .v15]⟩ rfl (ctrOut _) (by dsimp only; lit_decide)

end VG.Proof.Sm4.PPC64LE.Scrub
