module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Seed.Contract
public import VerifiedGarbage.Spec.Seed.Cbc
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.CfbFinal
public import VerifiedGarbage.Spec.Seed.Ofb
public import VerifiedGarbage.Spec.Seed.OfbFinal
public import VerifiedGarbage.Proof.Seed.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Seed.RISCV64.Frame
public import VerifiedGarbage.Proof.Seed.RISCV64.ModesVerified

import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Proof.Seed.CbcScratch
import VerifiedGarbage.Proof.Seed.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.Seed.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Seed.RISCV64.Lit
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit

meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Seed.Contract
meta import VerifiedGarbage.Spec.Seed.Cbc
meta import VerifiedGarbage.Spec.Seed.Cfb
meta import VerifiedGarbage.Spec.Seed.CfbFinal
meta import VerifiedGarbage.Spec.Seed.Ofb
meta import VerifiedGarbage.Spec.Seed.OfbFinal
meta import VerifiedGarbage.Proof.Seed.RISCV64.FbFinalVerified
meta import VerifiedGarbage.Proof.Seed.RISCV64.Frame
meta import VerifiedGarbage.Proof.Seed.RISCV64.ModesVerified
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Seed.CbcScratch
meta import VerifiedGarbage.Proof.Seed.FbScratch
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Seed.RISCV64.FbFinalLit
meta import VerifiedGarbage.Proof.Seed.RISCV64.Lit
meta import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit
/-!
# Seed on RISC-V, without secret residue

Each function, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within their buffers (`RISCV64.Scrub.PostOut`), as on x86-64
(`Proof/Seed/X86_64/Scrub.lean`).

The key expansion and ECB instead clear only the runs of doublewords that the residue
analysis (`RISCV64.rtaint`) finds may differ between two runs
(`RISCV64.Scrub.withScrubSel`, `scrubSel_noResidue`). Their code wipes most of
its own scratch space, which leaves few such doublewords, or none.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64.Scrub

open VG.Spec.Seed VG.RISCV64 VG.RISCV64.Scrub

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) : PostOut (Spec.Seed.expandKeyContract RISCV64.abi stack) (Spec.Seed.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.expandKeyPostOut_local _)

theorem ecbEncryptOut (stack : Nat) : PostOut (Spec.Seed.ecbContract RISCV64.abi .encrypt stack) (Spec.Seed.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.ecbPostOut_local _ .encrypt)

theorem ecbDecryptOut (stack : Nat) : PostOut (Spec.Seed.ecbContract RISCV64.abi .decrypt stack) (Spec.Seed.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.ecbPostOut_local _ .decrypt)

theorem cbcEncryptOut (stack : Nat) : PostOut (Spec.Seed.cbcEncryptChainedContract RISCV64.abi stack) (Spec.Seed.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cbcEncChainedPostOut_local _)

theorem cbcDecryptOut (stack : Nat) : PostOut (Spec.Seed.cbcDecryptChainedContract RISCV64.abi stack) (Spec.Seed.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cbcDecChainedPostOut_local _)

theorem cfbEncryptOut (stack : Nat) : PostOut (Spec.Seed.cfbEncryptContract RISCV64.abi stack) (Spec.Seed.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cfbEncPostOut_local _)

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (Spec.Seed.cfbEncryptFinalContract RISCV64.abi stack) (Spec.Seed.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptOut (stack : Nat) : PostOut (Spec.Seed.cfbDecryptContract RISCV64.abi stack) (Spec.Seed.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cfbDecPostOut_local _)

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (Spec.Seed.cfbDecryptFinalContract RISCV64.abi stack) (Spec.Seed.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem ofbOut (stack : Nat) : PostOut (Spec.Seed.ofbContract RISCV64.abi stack) (Spec.Seed.ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.ofbPostOut_local _)

theorem ofbFinalOut (stack : Nat) : PostOut (Spec.Seed.ofbFinalContract RISCV64.abi stack) (Spec.Seed.ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

/-! ## The registrations -/

/-- `Spec.Seed.expandKeyApi`. -/
def expandKeyReg : Registration Spec.Seed.expandKeyApi RISCV64.target :=
  withScrubSel { code := Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a2 129 Impl.Seed.RISCV64.expandKey, verified := Proof.Seed.RISCV64.expandKey_framed } [(1040, [(129, 1)])]
    (expandKeyOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (expandKeyOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a2 129 Impl.Seed.RISCV64.expandKey) 1040 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.Seed.ecbEncryptApi`. -/
def ecbEncryptReg : Registration Spec.Seed.ecbEncryptApi RISCV64.target :=
  withScrubSel { code := Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a3 129 (Impl.Seed.RISCV64.ecb .encrypt), verified := Proof.Seed.RISCV64.ecb_framed .encrypt } [(1040, [(129, 1)])]
    (ecbEncryptOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (ecbEncryptOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a3 129 (Impl.Seed.RISCV64.ecb .encrypt)) 1040 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.Seed.ecbDecryptApi`. -/
def ecbDecryptReg : Registration Spec.Seed.ecbDecryptApi RISCV64.target :=
  withScrubSel { code := Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a3 129 (Impl.Seed.RISCV64.ecb .decrypt), verified := Proof.Seed.RISCV64.ecb_framed .decrypt } [(1040, [(129, 1)])]
    (ecbDecryptOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (ecbDecryptOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a3 129 (Impl.Seed.RISCV64.ecb .decrypt)) 1040 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.Seed.cbcEncryptChainedApi`. -/
def cbcEncryptChainedReg : Registration Spec.Seed.cbcEncryptChainedApi RISCV64.target :=
  withScrub { code := Impl.Seed.RISCV64.cbcEncryptChained, verified := Proof.Seed.RISCV64.Modes.cbcEncryptChained_verified }
    (cbcEncryptOut _)

/-- `Spec.Seed.cbcDecryptChainedApi`. -/
def cbcDecryptChainedReg : Registration Spec.Seed.cbcDecryptChainedApi RISCV64.target :=
  withScrub { code := Impl.Seed.RISCV64.cbcDecryptChained, verified := Proof.Seed.RISCV64.Modes.cbcDecryptChained_verified }
    (cbcDecryptOut _)

/-- `Spec.Seed.cfbEncryptApi`. -/
def cfbEncryptReg : Registration Spec.Seed.cfbEncryptApi RISCV64.target :=
  withScrub { code := Impl.Seed.RISCV64.cfbEncrypt, verified := Proof.Seed.RISCV64.Modes.cfbEncrypt_verified }
    (cfbEncryptOut _)

/-- `Spec.Seed.cfbDecryptApi`. -/
def cfbDecryptReg : Registration Spec.Seed.cfbDecryptApi RISCV64.target :=
  withScrub { code := Impl.Seed.RISCV64.cfbDecrypt, verified := Proof.Seed.RISCV64.Modes.cfbDecrypt_verified }
    (cfbDecryptOut _)

/-- `Spec.Seed.cfbEncryptFinalApi`. -/
def cfbEncryptFinalReg : Registration Spec.Seed.cfbEncryptFinalApi RISCV64.target :=
  withScrub { code := Impl.Seed.RISCV64.cfbEncryptFinal, verified := Proof.Seed.RISCV64.Modes.cfbEncryptFinal_verified }
    (cfbEncryptFinalOut _)

/-- `Spec.Seed.cfbDecryptFinalApi`. -/
def cfbDecryptFinalReg : Registration Spec.Seed.cfbDecryptFinalApi RISCV64.target :=
  withScrub { code := Impl.Seed.RISCV64.cfbDecryptFinal, verified := Proof.Seed.RISCV64.Modes.cfbDecryptFinal_verified }
    (cfbDecryptFinalOut _)

/-- `Spec.Seed.ofbApi`. -/
def ofbReg : Registration Spec.Seed.ofbApi RISCV64.target :=
  withScrub { code := Impl.Seed.RISCV64.ofb, verified := Proof.Seed.RISCV64.Modes.ofb_verified }
    (ofbOut _)

/-- `Spec.Seed.ofbFinalApi`. -/
def ofbFinalReg : Registration Spec.Seed.ofbFinalApi RISCV64.target :=
  withScrub { code := Impl.Seed.RISCV64.ofbFinal, verified := Proof.Seed.RISCV64.Modes.ofbFinal_verified }
    (ofbFinalOut _)

end VG.Proof.Seed.RISCV64.Scrub
