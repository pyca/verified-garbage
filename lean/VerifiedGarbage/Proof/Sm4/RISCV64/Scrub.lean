module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.CfbFinal
public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Sm4.OfbFinal
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Spec.Sm4.CtrFinal
public import VerifiedGarbage.Proof.Sm4.RISCV64.CtrFinal
public import VerifiedGarbage.Proof.Sm4.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Sm4.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Sm4.RISCV64.Verified

import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Sm4.CbcScratch
import VerifiedGarbage.Proof.Sm4.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.Sm4.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit

/-!
# Sm4 on RISC-V, without secret residue

Each function, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within their buffers (`RISCV64.Scrub.PostOut`), as on x86-64
(`Proof/Sm4/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64.Scrub

open VG.Spec.Sm4 VG.RISCV64 VG.RISCV64.Scrub

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) : PostOut (Spec.Sm4.expandKeyContract RISCV64.abi stack) (Spec.Sm4.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.expandKeyPostOut_local _)

theorem ecbEncryptOut (stack : Nat) : PostOut (Spec.Sm4.ecbContract RISCV64.abi .encrypt stack) (Spec.Sm4.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ecbPostOut_local _ .encrypt)

theorem ecbDecryptOut (stack : Nat) : PostOut (Spec.Sm4.ecbContract RISCV64.abi .decrypt stack) (Spec.Sm4.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ecbPostOut_local _ .decrypt)

theorem cbcEncryptOut (stack : Nat) : PostOut (Spec.Sm4.cbcEncryptChainedContract RISCV64.abi stack) (Spec.Sm4.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cbcEncChainedPostOut_local _)

theorem cbcDecryptOut (stack : Nat) : PostOut (Spec.Sm4.cbcDecryptChainedContract RISCV64.abi stack) (Spec.Sm4.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cbcDecChainedPostOut_local _)

theorem cfbEncryptOut (stack : Nat) : PostOut (Spec.Sm4.cfbEncryptContract RISCV64.abi stack) (Spec.Sm4.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cfbEncPostOut_local _)

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (Spec.Sm4.cfbEncryptFinalContract RISCV64.abi stack) (Spec.Sm4.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptOut (stack : Nat) : PostOut (Spec.Sm4.cfbDecryptContract RISCV64.abi stack) (Spec.Sm4.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cfbDecPostOut_local _)

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (Spec.Sm4.cfbDecryptFinalContract RISCV64.abi stack) (Spec.Sm4.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem ofbOut (stack : Nat) : PostOut (Spec.Sm4.ofbContract RISCV64.abi stack) (Spec.Sm4.ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ofbPostOut_local _)

theorem ofbFinalOut (stack : Nat) : PostOut (Spec.Sm4.ofbFinalContract RISCV64.abi stack) (Spec.Sm4.ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

theorem ctrOut (stack : Nat) : PostOut (Spec.Sm4.ctrContract RISCV64.abi stack) (Spec.Sm4.ctrSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ctrPostOut_local _)

theorem ctrFinalOut (stack : Nat) : PostOut (Spec.Sm4.ctrFinalContract RISCV64.abi stack) (Spec.Sm4.ctrFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ctrFinalPostOut_local _)

/-! ## The registrations -/

/-- `Spec.Sm4.expandKeyApi`. -/
def expandKeyReg : Registration Spec.Sm4.expandKeyApi RISCV64.target :=
  withScrub { code := Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a2 396 Impl.Sm4.RISCV64.expandKey, verified := Proof.Sm4.RISCV64.expandKey_framed }
    (expandKeyOut _)

/-- `Spec.Sm4.ecbEncryptApi`. -/
def ecbEncryptReg : Registration Spec.Sm4.ecbEncryptApi RISCV64.target :=
  withScrub { code := Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a3 396 (Impl.Sm4.RISCV64.ecb .encrypt), verified := Proof.Sm4.RISCV64.ecb_framed .encrypt }
    (ecbEncryptOut _)

/-- `Spec.Sm4.ecbDecryptApi`. -/
def ecbDecryptReg : Registration Spec.Sm4.ecbDecryptApi RISCV64.target :=
  withScrub { code := Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a3 396 (Impl.Sm4.RISCV64.ecb .decrypt), verified := Proof.Sm4.RISCV64.ecb_framed .decrypt }
    (ecbDecryptOut _)

/-- `Spec.Sm4.cbcEncryptChainedApi`. -/
def cbcEncryptChainedReg : Registration Spec.Sm4.cbcEncryptChainedApi RISCV64.target :=
  withScrub { code := Impl.Sm4.RISCV64.cbcEncryptChained, verified := Proof.Sm4.RISCV64.Modes.cbcEncryptChained_verified }
    (cbcEncryptOut _)

/-- `Spec.Sm4.cbcDecryptChainedApi`. -/
def cbcDecryptChainedReg : Registration Spec.Sm4.cbcDecryptChainedApi RISCV64.target :=
  withScrub { code := Impl.Sm4.RISCV64.cbcDecryptChained, verified := Proof.Sm4.RISCV64.Modes.cbcDecryptChained_verified }
    (cbcDecryptOut _)

/-- `Spec.Sm4.cfbEncryptApi`. -/
def cfbEncryptReg : Registration Spec.Sm4.cfbEncryptApi RISCV64.target :=
  withScrub { code := Impl.Sm4.RISCV64.cfbEncrypt, verified := Proof.Sm4.RISCV64.Modes.cfbEncrypt_verified }
    (cfbEncryptOut _)

/-- `Spec.Sm4.cfbDecryptApi`. -/
def cfbDecryptReg : Registration Spec.Sm4.cfbDecryptApi RISCV64.target :=
  withScrub { code := Impl.Sm4.RISCV64.cfbDecrypt, verified := Proof.Sm4.RISCV64.Modes.cfbDecrypt_verified }
    (cfbDecryptOut _)

/-- `Spec.Sm4.cfbEncryptFinalApi`. -/
def cfbEncryptFinalReg : Registration Spec.Sm4.cfbEncryptFinalApi RISCV64.target :=
  withScrub { code := Impl.Sm4.RISCV64.cfbEncryptFinal, verified := Proof.Sm4.RISCV64.Modes.cfbEncryptFinal_verified }
    (cfbEncryptFinalOut _)

/-- `Spec.Sm4.cfbDecryptFinalApi`. -/
def cfbDecryptFinalReg : Registration Spec.Sm4.cfbDecryptFinalApi RISCV64.target :=
  withScrub { code := Impl.Sm4.RISCV64.cfbDecryptFinal, verified := Proof.Sm4.RISCV64.Modes.cfbDecryptFinal_verified }
    (cfbDecryptFinalOut _)

/-- `Spec.Sm4.ctrApi`. -/
def ctrReg : Registration Spec.Sm4.ctrApi RISCV64.target :=
  withScrub { code := Impl.Sm4.RISCV64.ctr, verified := Proof.Sm4.RISCV64.Modes.ctr_verified }
    (ctrOut _)

/-- `Spec.Sm4.ctrFinalApi`. -/
def ctrFinalReg : Registration Spec.Sm4.ctrFinalApi RISCV64.target :=
  withScrub { code := Impl.StackScratch.RISCV64.withStackScratchWiped 80 .a4 10 Impl.Sm4.RISCV64.ctrFinal, verified := Proof.Sm4.RISCV64.CtrFinal.ctrFinal_framed }
    (ctrFinalOut _)

/-- `Spec.Sm4.ofbApi`. -/
def ofbReg : Registration Spec.Sm4.ofbApi RISCV64.target :=
  withScrub { code := Impl.Sm4.RISCV64.ofb, verified := Proof.Sm4.RISCV64.Modes.ofb_verified }
    (ofbOut _)

/-- `Spec.Sm4.ofbFinalApi`. -/
def ofbFinalReg : Registration Spec.Sm4.ofbFinalApi RISCV64.target :=
  withScrub { code := Impl.Sm4.RISCV64.ofbFinal, verified := Proof.Sm4.RISCV64.Modes.ofbFinal_verified }
    (ofbFinalOut _)

end VG.Proof.Sm4.RISCV64.Scrub
