module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubWiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Seed.Contract
public import VerifiedGarbage.Spec.Seed.Cbc
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.CfbFinal
public import VerifiedGarbage.Spec.Seed.Ofb
public import VerifiedGarbage.Spec.Seed.OfbFinal
public import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.Frame
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.Verified
import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Proof.Seed.CbcScratch
import VerifiedGarbage.Proof.Seed.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch

/-!
# SEED on PPC64LE, without secret residue

Key expansion and the CBC, CFB128 and OFB functions zero their whole frame
themselves before they release it (`withStackScratchWiped`), and have no
frames of their own inside it, so they need only the clearing of the
volatile registers they write after them (`PPC64LE.Scrub.withScrubWiped`).
ECB, whose wiped frame holds the frame of the call it makes, is followed by
`Impl.Scrub.PPC64LE.scrubTail` with its stack wiped (`PPC64LE.Scrub.withScrub`).
Their postconditions read the memory on return only within their buffers, by
the target-independent lemmas RISC-V's and x86-64's proofs use
(`Proof/Seed/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) : PostOut (Spec.Seed.expandKeyContract PPC64LE.abi stack) (Spec.Seed.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.expandKeyPostOut_local _)

theorem ecbEncryptOut (stack : Nat) : PostOut (Spec.Seed.ecbContract PPC64LE.abi .encrypt stack) (Spec.Seed.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.ecbPostOut_local _ .encrypt)

theorem ecbDecryptOut (stack : Nat) : PostOut (Spec.Seed.ecbContract PPC64LE.abi .decrypt stack) (Spec.Seed.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.ecbPostOut_local _ .decrypt)

theorem cbcEncryptOut (stack : Nat) : PostOut (Spec.Seed.cbcEncryptChainedContract PPC64LE.abi stack) (Spec.Seed.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cbcEncChainedPostOut_local _)

theorem cbcDecryptOut (stack : Nat) : PostOut (Spec.Seed.cbcDecryptChainedContract PPC64LE.abi stack) (Spec.Seed.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cbcDecChainedPostOut_local _)

theorem cfbEncryptOut (stack : Nat) : PostOut (Spec.Seed.cfbEncryptContract PPC64LE.abi stack) (Spec.Seed.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cfbEncPostOut_local _)

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (Spec.Seed.cfbEncryptFinalContract PPC64LE.abi stack) (Spec.Seed.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptOut (stack : Nat) : PostOut (Spec.Seed.cfbDecryptContract PPC64LE.abi stack) (Spec.Seed.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cfbDecPostOut_local _)

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (Spec.Seed.cfbDecryptFinalContract PPC64LE.abi stack) (Spec.Seed.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem ofbOut (stack : Nat) : PostOut (Spec.Seed.ofbContract PPC64LE.abi stack) (Spec.Seed.ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.ofbPostOut_local _)

theorem ofbFinalOut (stack : Nat) : PostOut (Spec.Seed.ofbFinalContract PPC64LE.abi stack) (Spec.Seed.ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

/-! ## The registrations -/

/-- `Spec.Seed.expandKeyApi`. -/
def expandKeyReg : Registration Spec.Seed.expandKeyApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1072 .r5 130 Impl.Seed.PPC64LE.expandKey
      verified := Proof.Seed.PPC64LE.expandKey_framed }
    1072 .r5 130 Impl.Seed.PPC64LE.expandKey rfl (expandKeyOut _)

/-- `Spec.Seed.ecbEncryptApi`. -/
def ecbEncryptReg : Registration Spec.Seed.ecbEncryptApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1120 .r6 136 (Impl.Seed.PPC64LE.ecbCall .encrypt)
      verified := Proof.Seed.PPC64LE.ecbCall_framed .encrypt }
    (ecbEncryptOut _)

/-- `Spec.Seed.ecbDecryptApi`. -/
def ecbDecryptReg : Registration Spec.Seed.ecbDecryptApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1120 .r6 136 (Impl.Seed.PPC64LE.ecbCall .decrypt)
      verified := Proof.Seed.PPC64LE.ecbCall_framed .decrypt }
    (ecbDecryptOut _)

/-- `Spec.Seed.cbcEncryptChainedApi`. -/
def cbcEncryptChainedReg : Registration Spec.Seed.cbcEncryptChainedApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cbcEncryptChained
      verified := Proof.Seed.PPC64LE.cbcEnc_framed Proof.Seed.PPC64LE.Modes.cbcEncryptChained_verified }
    1184 .r7 144 Impl.Seed.PPC64LE.cbcEncryptChained rfl (cbcEncryptOut _)

/-- `Spec.Seed.cbcDecryptChainedApi`. -/
def cbcDecryptChainedReg : Registration Spec.Seed.cbcDecryptChainedApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1424 .r7 174 Impl.Seed.PPC64LE.cbcDecryptChained
      verified := Proof.Seed.PPC64LE.cbcDec_framed Proof.Seed.PPC64LE.Modes.cbcDecryptChained_verified }
    1424 .r7 174 Impl.Seed.PPC64LE.cbcDecryptChained rfl (cbcDecryptOut _)

/-- `Spec.Seed.cfbEncryptApi`. -/
def cfbEncryptReg : Registration Spec.Seed.cfbEncryptApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cfbEncrypt
      verified := Proof.Seed.PPC64LE.cfbEnc_framed Proof.Seed.PPC64LE.Modes.cfbEncrypt_verified }
    1184 .r7 144 Impl.Seed.PPC64LE.cfbEncrypt rfl (cfbEncryptOut _)

/-- `Spec.Seed.cfbDecryptApi`. -/
def cfbDecryptReg : Registration Spec.Seed.cfbDecryptApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1424 .r7 174 Impl.Seed.PPC64LE.cfbDecrypt
      verified := Proof.Seed.PPC64LE.cfbDec_framed Proof.Seed.PPC64LE.Modes.cfbDecrypt_verified }
    1424 .r7 174 Impl.Seed.PPC64LE.cfbDecrypt rfl (cfbDecryptOut _)

/-- `Spec.Seed.cfbEncryptFinalApi`. -/
def cfbEncryptFinalReg : Registration Spec.Seed.cfbEncryptFinalApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cfbEncryptFinal
      verified := Proof.Seed.PPC64LE.FbFinal.cfbEncryptFinal_framed }
    1184 .r7 144 Impl.Seed.PPC64LE.cfbEncryptFinal rfl (cfbEncryptFinalOut _)

/-- `Spec.Seed.cfbDecryptFinalApi`. -/
def cfbDecryptFinalReg : Registration Spec.Seed.cfbDecryptFinalApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cfbDecryptFinal
      verified := Proof.Seed.PPC64LE.FbFinal.cfbDecryptFinal_framed }
    1184 .r7 144 Impl.Seed.PPC64LE.cfbDecryptFinal rfl (cfbDecryptFinalOut _)

/-- `Spec.Seed.ofbApi`. -/
def ofbReg : Registration Spec.Seed.ofbApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.ofb
      verified := Proof.Seed.PPC64LE.ofb_framed Proof.Seed.PPC64LE.Modes.ofb_verified }
    1184 .r7 144 Impl.Seed.PPC64LE.ofb rfl (ofbOut _)

/-- `Spec.Seed.ofbFinalApi`. -/
def ofbFinalReg : Registration Spec.Seed.ofbFinalApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.ofbFinal
      verified := Proof.Seed.PPC64LE.FbFinal.ofbFinal_framed }
    1184 .r7 144 Impl.Seed.PPC64LE.ofbFinal rfl (ofbFinalOut _)

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
    ofbReg.residue.isSome ∧
    ofbFinalReg.residue.isSome := by decide

end VG.Proof.Seed.PPC64LE.Scrub
