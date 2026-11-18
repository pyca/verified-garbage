module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.TripleDes.Contract
public import VerifiedGarbage.Spec.TripleDes.Cbc
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Spec.TripleDes.Cfb8
public import VerifiedGarbage.Spec.TripleDes.CfbFinal
public import VerifiedGarbage.Spec.TripleDes.Ofb
public import VerifiedGarbage.Spec.TripleDes.OfbFinal
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Verified
public import VerifiedGarbage.Proof.TripleDes.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesVerified

import VerifiedGarbage.Proof.TripleDes.Scratch
import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.TripleDes.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Lit
import VerifiedGarbage.Proof.TripleDes.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit

/-!
# TripleDes on RISC-V, without secret residue

Each function, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within their buffers (`RISCV64.Scrub.PostOut`), as on x86-64
(`Proof/TripleDes/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Scrub

open VG.Spec.TripleDes VG.RISCV64 VG.RISCV64.Scrub

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) : PostOut (Spec.TripleDes.expandKeyContract RISCV64.abi stack) (Spec.TripleDes.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.expandKeyPostOut_local _)

theorem cbcEncryptOut (stack : Nat) : PostOut (Spec.TripleDes.cbcEncryptChainedContract RISCV64.abi stack) (Spec.TripleDes.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cbcEncChainedPostOut_local _)

theorem cfbEncryptOut (stack : Nat) : PostOut (Spec.TripleDes.cfbEncryptContract RISCV64.abi stack) (Spec.TripleDes.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfbEncPostOut_local _)

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (Spec.TripleDes.cfbEncryptFinalContract RISCV64.abi stack) (Spec.TripleDes.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (Spec.TripleDes.cfbDecryptFinalContract RISCV64.abi stack) (Spec.TripleDes.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem cfb8EncryptOut (stack : Nat) : PostOut (Spec.TripleDes.cfb8EncryptContract RISCV64.abi stack) (Spec.TripleDes.cfb8Sig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfb8EncPostOut_local _)

theorem cfb8DecryptOut (stack : Nat) : PostOut (Spec.TripleDes.cfb8DecryptContract RISCV64.abi stack) (Spec.TripleDes.cfb8Sig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfb8DecPostOut_local _)

theorem ofbOut (stack : Nat) : PostOut (Spec.TripleDes.ofbContract RISCV64.abi stack) (Spec.TripleDes.ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.ofbPostOut_local _)

theorem ofbFinalOut (stack : Nat) : PostOut (Spec.TripleDes.ofbFinalContract RISCV64.abi stack) (Spec.TripleDes.ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

theorem ecbOut (d : Spec.TripleDes.Direction) (stack : Nat) : PostOut (Spec.TripleDes.ecbContract RISCV64.abi d stack) (Spec.TripleDes.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.ecbPostOut_local _ d)

/-! ## The registrations -/

/-- `Spec.TripleDes.expandKeyApi`. -/
def expandKeyReg : Registration Spec.TripleDes.expandKeyApi RISCV64.target :=
  withScrub { code := Impl.TripleDes.RISCV64.Key.expandKey, verified := Proof.TripleDes.RISCV64.Key.verified }
    (expandKeyOut _)

/-- `Spec.TripleDes.ecbEncryptApi`. -/
def ecbEncryptReg : Registration Spec.TripleDes.ecbEncryptApi RISCV64.target :=
  withScrub { code := Impl.TripleDes.RISCV64.Bitslice.encrypt, verified := Proof.TripleDes.RISCV64.Bitsliced.encrypt_verified }
    (ecbOut .encrypt _)

/-- `Spec.TripleDes.ecbDecryptApi`. -/
def ecbDecryptReg : Registration Spec.TripleDes.ecbDecryptApi RISCV64.target :=
  withScrub { code := Impl.TripleDes.RISCV64.Bitslice.decrypt, verified := Proof.TripleDes.RISCV64.Bitsliced.decrypt_verified }
    (ecbOut .decrypt _)

/-- `Spec.TripleDes.cbcEncryptChainedApi`. -/
def cbcEncryptChainedReg : Registration Spec.TripleDes.cbcEncryptChainedApi RISCV64.target :=
  withScrub { code := Impl.TripleDes.RISCV64.cbcEncryptChained, verified := Proof.TripleDes.RISCV64.Modes.cbcEncryptChained_verified }
    (cbcEncryptOut _)

/-- `Spec.TripleDes.cfbEncryptApi`. -/
def cfbEncryptReg : Registration Spec.TripleDes.cfbEncryptApi RISCV64.target :=
  withScrub { code := Impl.TripleDes.RISCV64.cfbEncrypt, verified := Proof.TripleDes.RISCV64.Modes.cfbEncrypt_verified }
    (cfbEncryptOut _)

/-- `Spec.TripleDes.cfbEncryptFinalApi`. -/
def cfbEncryptFinalReg : Registration Spec.TripleDes.cfbEncryptFinalApi RISCV64.target :=
  withScrub { code := Impl.TripleDes.RISCV64.cfbEncryptFinal, verified := Proof.TripleDes.RISCV64.Modes.cfbEncryptFinal_verified }
    (cfbEncryptFinalOut _)

/-- `Spec.TripleDes.cfbDecryptFinalApi`. -/
def cfbDecryptFinalReg : Registration Spec.TripleDes.cfbDecryptFinalApi RISCV64.target :=
  withScrub { code := Impl.TripleDes.RISCV64.cfbDecryptFinal, verified := Proof.TripleDes.RISCV64.Modes.cfbDecryptFinal_verified }
    (cfbDecryptFinalOut _)

/-- `Spec.TripleDes.cfb8EncryptApi`. -/
def cfb8EncryptReg : Registration Spec.TripleDes.cfb8EncryptApi RISCV64.target :=
  withScrub { code := Impl.TripleDes.RISCV64.cfb8Encrypt, verified := Proof.TripleDes.RISCV64.Modes.cfb8Encrypt_verified }
    (cfb8EncryptOut _)

/-- `Spec.TripleDes.cfb8DecryptApi`. -/
def cfb8DecryptReg : Registration Spec.TripleDes.cfb8DecryptApi RISCV64.target :=
  withScrub { code := Impl.TripleDes.RISCV64.cfb8Decrypt, verified := Proof.TripleDes.RISCV64.Modes.cfb8Decrypt_verified }
    (cfb8DecryptOut _)

/-- `Spec.TripleDes.ofbApi`. -/
def ofbReg : Registration Spec.TripleDes.ofbApi RISCV64.target :=
  withScrub { code := Impl.TripleDes.RISCV64.ofb, verified := Proof.TripleDes.RISCV64.Modes.ofb_verified }
    (ofbOut _)

/-- `Spec.TripleDes.ofbFinalApi`. -/
def ofbFinalReg : Registration Spec.TripleDes.ofbFinalApi RISCV64.target :=
  withScrub { code := Impl.TripleDes.RISCV64.ofbFinal, verified := Proof.TripleDes.RISCV64.Modes.ofbFinal_verified }
    (ofbFinalOut _)

end VG.Proof.TripleDes.RISCV64.Scrub
