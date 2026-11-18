module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubWiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.TripleDes.Contract
public import VerifiedGarbage.Spec.TripleDes.Cbc
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Spec.TripleDes.Cfb8
public import VerifiedGarbage.Spec.TripleDes.CfbFinal
public import VerifiedGarbage.Spec.TripleDes.Ofb
public import VerifiedGarbage.Spec.TripleDes.OfbFinal
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Verified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Frame
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.TripleDes.Scratch
import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.TripleDes.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch

/-!
# Triple DES on PPC64LE, without secret residue

Key expansion, which has no frames, is followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.withScrub`), which wipes no
stack for it. The ECB, CBC, CFB64, CFB8 and OFB functions zero their whole
frame themselves before they release it (`withStackScratchWiped`), and have
no frames of their own inside it, so they need only the clearing of the
volatile registers they write after them (`PPC64LE.Scrub.withScrubWiped`).
Their postconditions read the memory on return only within their buffers, by
the target-independent lemmas RISC-V's and x86-64's proofs use
(`Proof/TripleDes/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) : PostOut (Spec.TripleDes.expandKeyContract PPC64LE.abi stack) (Spec.TripleDes.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.expandKeyPostOut_local _)

theorem cbcEncryptOut (stack : Nat) : PostOut (Spec.TripleDes.cbcEncryptChainedContract PPC64LE.abi stack) (Spec.TripleDes.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cbcEncChainedPostOut_local _)

theorem cfbEncryptOut (stack : Nat) : PostOut (Spec.TripleDes.cfbEncryptContract PPC64LE.abi stack) (Spec.TripleDes.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfbEncPostOut_local _)

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (Spec.TripleDes.cfbEncryptFinalContract PPC64LE.abi stack) (Spec.TripleDes.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (Spec.TripleDes.cfbDecryptFinalContract PPC64LE.abi stack) (Spec.TripleDes.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem cfb8EncryptOut (stack : Nat) : PostOut (Spec.TripleDes.cfb8EncryptContract PPC64LE.abi stack) (Spec.TripleDes.cfb8Sig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfb8EncPostOut_local _)

theorem cfb8DecryptOut (stack : Nat) : PostOut (Spec.TripleDes.cfb8DecryptContract PPC64LE.abi stack) (Spec.TripleDes.cfb8Sig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfb8DecPostOut_local _)

theorem ofbOut (stack : Nat) : PostOut (Spec.TripleDes.ofbContract PPC64LE.abi stack) (Spec.TripleDes.ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.ofbPostOut_local _)

theorem ofbFinalOut (stack : Nat) : PostOut (Spec.TripleDes.ofbFinalContract PPC64LE.abi stack) (Spec.TripleDes.ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

theorem ecbOut (d : Spec.TripleDes.Direction) (stack : Nat) : PostOut (Spec.TripleDes.ecbContract PPC64LE.abi d stack) (Spec.TripleDes.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.ecbPostOut_local _ d)

theorem cbcDecryptOut (stack : Nat) : PostOut (Spec.TripleDes.cbcDecryptChainedContract PPC64LE.abi stack) (Spec.TripleDes.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cbcDecChainedPostOut_local _)

theorem cfbDecryptOut (stack : Nat) : PostOut (Spec.TripleDes.cfbDecryptContract PPC64LE.abi stack) (Spec.TripleDes.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfbDecPostOut_local _)

/-! ## The registrations -/

/-- `Spec.TripleDes.expandKeyApi`. -/
def expandKeyReg : Registration Spec.TripleDes.expandKeyApi PPC64LE.target :=
  withScrub { code := Impl.TripleDes.PPC64LE.Key.expandKey, verified := Proof.TripleDes.PPC64LE.Key.verified } (expandKeyOut _)

/-- `Spec.TripleDes.ecbEncryptApi`. -/
def ecbEncryptReg : Registration Spec.TripleDes.ecbEncryptApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1056 .r6 128 Impl.TripleDes.PPC64LE.Bitslice.encrypt
      verified := Proof.TripleDes.PPC64LE.ecb_framed Proof.TripleDes.PPC64LE.Bitsliced.encrypt_verified }
    1056 .r6 128 Impl.TripleDes.PPC64LE.Bitslice.encrypt rfl (ecbOut .encrypt _)

/-- `Spec.TripleDes.ecbDecryptApi`. -/
def ecbDecryptReg : Registration Spec.TripleDes.ecbDecryptApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1056 .r6 128 Impl.TripleDes.PPC64LE.Bitslice.decrypt
      verified := Proof.TripleDes.PPC64LE.ecb_framed Proof.TripleDes.PPC64LE.Bitsliced.decrypt_verified }
    1056 .r6 128 Impl.TripleDes.PPC64LE.Bitslice.decrypt rfl (ecbOut .decrypt _)

/-- `Spec.TripleDes.cbcEncryptChainedApi`. -/
def cbcEncryptChainedReg : Registration Spec.TripleDes.cbcEncryptChainedApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cbcEncryptChained
      verified := Proof.TripleDes.PPC64LE.cbcEnc_framed Proof.TripleDes.PPC64LE.Modes.cbcEncryptChained_verified }
    608 .r7 72 Impl.TripleDes.PPC64LE.cbcEncryptChained rfl (cbcEncryptOut _)

/-- `Spec.TripleDes.cbcDecryptChainedApi`. -/
def cbcDecryptChainedReg : Registration Spec.TripleDes.cbcDecryptChainedApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1632 .r7 200 Impl.TripleDes.PPC64LE.cbcDecryptChained
      verified := Proof.TripleDes.PPC64LE.cbcDec_framed Proof.TripleDes.PPC64LE.Modes.cbcDecryptChained_verified }
    1632 .r7 200 Impl.TripleDes.PPC64LE.cbcDecryptChained rfl (cbcDecryptOut _)

/-- `Spec.TripleDes.cfbEncryptApi`. -/
def cfbEncryptReg : Registration Spec.TripleDes.cfbEncryptApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfbEncrypt
      verified := Proof.TripleDes.PPC64LE.cfbEnc_framed Proof.TripleDes.PPC64LE.Modes.cfbEncrypt_verified }
    608 .r7 72 Impl.TripleDes.PPC64LE.cfbEncrypt rfl (cfbEncryptOut _)

/-- `Spec.TripleDes.cfbDecryptApi`. -/
def cfbDecryptReg : Registration Spec.TripleDes.cfbDecryptApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1632 .r7 200 Impl.TripleDes.PPC64LE.cfbDecrypt
      verified := Proof.TripleDes.PPC64LE.cfbDec_framed Proof.TripleDes.PPC64LE.Modes.cfbDecrypt_verified }
    1632 .r7 200 Impl.TripleDes.PPC64LE.cfbDecrypt rfl (cfbDecryptOut _)

/-- `Spec.TripleDes.cfbEncryptFinalApi`. -/
def cfbEncryptFinalReg : Registration Spec.TripleDes.cfbEncryptFinalApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfbEncryptFinal
      verified := Proof.TripleDes.PPC64LE.FbFinal.cfbEncryptFinal_framed }
    608 .r7 72 Impl.TripleDes.PPC64LE.cfbEncryptFinal rfl (cfbEncryptFinalOut _)

/-- `Spec.TripleDes.cfbDecryptFinalApi`. -/
def cfbDecryptFinalReg : Registration Spec.TripleDes.cfbDecryptFinalApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfbDecryptFinal
      verified := Proof.TripleDes.PPC64LE.FbFinal.cfbDecryptFinal_framed }
    608 .r7 72 Impl.TripleDes.PPC64LE.cfbDecryptFinal rfl (cfbDecryptFinalOut _)

/-- `Spec.TripleDes.cfb8EncryptApi`. -/
def cfb8EncryptReg : Registration Spec.TripleDes.cfb8EncryptApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfb8Encrypt
      verified := Proof.TripleDes.PPC64LE.cfb8Enc_framed Proof.TripleDes.PPC64LE.Modes.cfb8Encrypt_verified }
    608 .r7 72 Impl.TripleDes.PPC64LE.cfb8Encrypt rfl (cfb8EncryptOut _)

/-- `Spec.TripleDes.cfb8DecryptApi`. -/
def cfb8DecryptReg : Registration Spec.TripleDes.cfb8DecryptApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfb8Decrypt
      verified := Proof.TripleDes.PPC64LE.cfb8Dec_framed Proof.TripleDes.PPC64LE.Modes.cfb8Decrypt_verified }
    608 .r7 72 Impl.TripleDes.PPC64LE.cfb8Decrypt rfl (cfb8DecryptOut _)

/-- `Spec.TripleDes.ofbApi`. -/
def ofbReg : Registration Spec.TripleDes.ofbApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.ofb
      verified := Proof.TripleDes.PPC64LE.ofb_framed Proof.TripleDes.PPC64LE.Modes.ofb_verified }
    608 .r7 72 Impl.TripleDes.PPC64LE.ofb rfl (ofbOut _)

/-- `Spec.TripleDes.ofbFinalApi`. -/
def ofbFinalReg : Registration Spec.TripleDes.ofbFinalApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.ofbFinal
      verified := Proof.TripleDes.PPC64LE.FbFinal.ofbFinal_framed }
    608 .r7 72 Impl.TripleDes.PPC64LE.ofbFinal rfl (ofbFinalOut _)

/-- All are scrubbed: the side conditions of `withScrub` and `withScrubWiped` hold. -/
example : expandKeyReg.residue.isSome ∧
    ecbEncryptReg.residue.isSome ∧
    ecbDecryptReg.residue.isSome ∧
    cbcEncryptChainedReg.residue.isSome ∧
    cbcDecryptChainedReg.residue.isSome ∧
    cfbEncryptReg.residue.isSome ∧
    cfbDecryptReg.residue.isSome ∧
    cfbEncryptFinalReg.residue.isSome ∧
    cfbDecryptFinalReg.residue.isSome ∧
    cfb8EncryptReg.residue.isSome ∧
    cfb8DecryptReg.residue.isSome ∧
    ofbReg.residue.isSome ∧
    ofbFinalReg.residue.isSome := by decide

end VG.Proof.TripleDes.PPC64LE.Scrub
