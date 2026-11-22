module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
public import VerifiedGarbage.Impl.TripleDes.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.TripleDes.Arm.Frame
public import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Verified
public import VerifiedGarbage.Proof.TripleDes.Arm.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.Arm.CbcVerified
public import VerifiedGarbage.Proof.TripleDes.Arm.FbVerified
public import VerifiedGarbage.Proof.TripleDes.Arm.FbFinalVerified
public import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.WideVerified
public import VerifiedGarbage.Impl.TripleDes.Arm.FbFinal
public import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
import VerifiedGarbage.Proof.TripleDes.Scratch
import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.TripleDes.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
meta import VerifiedGarbage.Impl.TripleDes.Arm.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.TripleDes.Arm.Frame
meta import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Verified
meta import VerifiedGarbage.Proof.TripleDes.Arm.Key.Verified
meta import VerifiedGarbage.Proof.TripleDes.Arm.CbcVerified
meta import VerifiedGarbage.Proof.TripleDes.Arm.FbVerified
meta import VerifiedGarbage.Proof.TripleDes.Arm.FbFinalVerified
meta import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.WideVerified
meta import VerifiedGarbage.Impl.TripleDes.Arm.FbFinal
meta import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
meta import VerifiedGarbage.Proof.TripleDes.Scratch
meta import VerifiedGarbage.Proof.TripleDes.CbcScratch
meta import VerifiedGarbage.Proof.TripleDes.FbScratch
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# Triple DES on ARMv7, without secret residue

Every public function of Triple DES on ARMv7 keeps its working space in a
frame: key expansion's 512 bytes and ECB's 1024 (`withRegScratchWiped`),
the batched CBC and CFB64 decryption's 1040, and the modes one block at a
time 64 bytes of their own around ECB's 1024 (`withStackScratchWiped`).
None makes an indirect call, and their postconditions read the memory on
return only within their buffers (`Arm.Scrub.PostOut`, from the lemmas of
`Proof/TripleDes/Scratch.lean`, `CbcScratch.lean`, `FbScratch.lean` and
`Proof/Modes/CfbFinalScratch.lean` that x86-64 uses too). Each wipes its own working space, and is
emitted followed by a wipe of only the words of the stack its contract
reserves that the residue analysis finds may differ between two runs
(`Impl.Scrub.Arm.scrubSel`), and by instructions that set the
registers a callee may change, but the result, and the flags to constants
(`Impl.TripleDes.Arm.Fn`). `Fn` below states that each returns without
secret residue (`Arm.Scrub.verifiedScrubbedSel`, whose analysis,
`Arm.rtaint`, the kernel evaluates here: `taint_decide_ct`), which is what
its registration binds.

The modes call the ECB artifacts as they are emitted, cleanup included
(`Impl.TripleDes.Arm.ecbCore`), whose theorems are in `ModeCore.lean`: the
analysis of each mode covers the frame of that call.
-/

@[expose] public section

namespace VG.Proof.TripleDes.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Modes.Arm

/-! ## The postconditions -/

theorem expandKeyOut : PostOut (Spec.TripleDes.expandKeyContract Arm.abi 512) (Spec.TripleDes.expandKeySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.expandKeyPostOut_local _)

theorem cbcEncryptOut :
    PostOut (Spec.TripleDes.cbcEncryptChainedContract Arm.abi 1088) (Spec.TripleDes.cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cbcEncChainedPostOut_local _)

theorem cbcDecryptOut :
    PostOut (Spec.TripleDes.cbcDecryptChainedContract Arm.abi 1040) (Spec.TripleDes.cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cbcDecChainedPostOut_local _)

theorem cfbEncryptOut : PostOut (Spec.TripleDes.cfbEncryptContract Arm.abi 1088) (Spec.TripleDes.cfbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfbEncPostOut_local _)

theorem cfbDecryptOut : PostOut (Spec.TripleDes.cfbDecryptContract Arm.abi 1040) (Spec.TripleDes.cfbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfbDecPostOut_local _)

theorem cfbEncryptFinalOut :
    PostOut (Spec.TripleDes.cfbEncryptFinalContract Arm.abi 1088) (Spec.TripleDes.cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptFinalOut :
    PostOut (Spec.TripleDes.cfbDecryptFinalContract Arm.abi 1088) (Spec.TripleDes.cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem cfb8EncryptOut : PostOut (Spec.TripleDes.cfb8EncryptContract Arm.abi 1088) (Spec.TripleDes.cfb8Sig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfb8EncPostOut_local _)

theorem cfb8DecryptOut : PostOut (Spec.TripleDes.cfb8DecryptContract Arm.abi 1088) (Spec.TripleDes.cfb8Sig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfb8DecPostOut_local _)

theorem ofbOut : PostOut (Spec.TripleDes.ofbContract Arm.abi 1088) (Spec.TripleDes.ofbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.ofbPostOut_local _)

theorem ofbFinalOut : PostOut (Spec.TripleDes.ofbFinalContract Arm.abi 1088) (Spec.TripleDes.ofbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

/-! ## The stack the functions zeroed in a loop use (`scrubAll`, `Arm.Scrub.CodeOk`) -/

theorem expandKey_code :
    CodeOk (Impl.StackScratch.Arm.withRegScratch 512 .r3 Impl.TripleDes.Arm.Key.expandKey) 512 := by
  lit_decide

theorem cbcDecrypt_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 1040 0 Impl.TripleDes.Arm.Wide.cbcDecrypt) 1040 := by
  lit_decide

theorem cfbDecrypt_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 1040 0 Impl.TripleDes.Arm.Wide.cfbDecrypt) 1040 := by
  lit_decide

end VG.Proof.TripleDes.Arm.Scrub

namespace VG.Proof.TripleDes.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Modes.Arm

/-- `vg_triple_des_expand_key`. -/
theorem expandKey :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.expandKey (Spec.TripleDes.expandKeyContract Arm.abi 512) 0 :=
  verifiedScrubbedAll (api := Spec.TripleDes.expandKeyApi)
    { code := Impl.StackScratch.Arm.withRegScratch 512 .r3 Impl.TripleDes.Arm.Key.expandKey
      verified := Proof.TripleDes.Arm.expandKey_framed }
    Scrub.expandKeyOut
    (scrubSideF_of Scrub.expandKey_code (by decide) _)

/-- `vg_triple_des_cbc_encrypt_chained`. -/
theorem cbcEncrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cbcEncrypt (Spec.TripleDes.cbcEncryptChainedContract Arm.abi 1088) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cbcEncryptChainedApi) (W := 1088)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cbcEncryptChained
      verified := Proof.TripleDes.Arm.cbcEncryptChained_framed }
    Impl.TripleDes.Arm.Fn.modeWords []
    Scrub.cbcEncryptOut
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_cbc_decrypt_chained`. -/
theorem cbcDecrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cbcDecrypt (Spec.TripleDes.cbcDecryptChainedContract Arm.abi 1040) 0 :=
  verifiedScrubbedAll (api := Spec.TripleDes.cbcDecryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratch 1040 0 Impl.TripleDes.Arm.Wide.cbcDecrypt
      verified := Proof.TripleDes.Arm.Bitsliced.cbcDecrypt_framed }
    Scrub.cbcDecryptOut
    (scrubSideF_of Scrub.cbcDecrypt_code (by decide) _)

/-- `vg_triple_des_cfb64_encrypt`. -/
theorem cfbEncrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cfbEncrypt (Spec.TripleDes.cfbEncryptContract Arm.abi 1088) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfbEncryptApi) (W := 1088)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbEncrypt
      verified := Proof.TripleDes.Arm.cfbEncrypt_framed }
    Impl.TripleDes.Arm.Fn.modeWords []
    Scrub.cfbEncryptOut
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_cfb64_decrypt`. -/
theorem cfbDecrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cfbDecrypt (Spec.TripleDes.cfbDecryptContract Arm.abi 1040) 0 :=
  verifiedScrubbedAll (api := Spec.TripleDes.cfbDecryptApi)
    { code := Impl.StackScratch.Arm.withStackScratch 1040 0 Impl.TripleDes.Arm.Wide.cfbDecrypt
      verified := Proof.TripleDes.Arm.Bitsliced.cfbDecrypt_framed }
    Scrub.cfbDecryptOut
    (scrubSideF_of Scrub.cfbDecrypt_code (by decide) _)

/-- `vg_triple_des_cfb64_encrypt_final`. -/
theorem cfbEncryptFinal :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cfbEncryptFinal (Spec.TripleDes.cfbEncryptFinalContract Arm.abi 1088) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfbEncryptFinalApi) (W := 1088)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbEncryptFinal
      verified := Proof.TripleDes.Arm.cfbEncryptFinal_framed }
    Impl.TripleDes.Arm.Fn.modeWords []
    Scrub.cfbEncryptFinalOut
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_cfb64_decrypt_final`. -/
theorem cfbDecryptFinal :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cfbDecryptFinal (Spec.TripleDes.cfbDecryptFinalContract Arm.abi 1088) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfbDecryptFinalApi) (W := 1088)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbDecryptFinal
      verified := Proof.TripleDes.Arm.cfbDecryptFinal_framed }
    Impl.TripleDes.Arm.Fn.modeWords []
    Scrub.cfbDecryptFinalOut
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_cfb8_encrypt`. -/
theorem cfb8Encrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cfb8Encrypt (Spec.TripleDes.cfb8EncryptContract Arm.abi 1088) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfb8EncryptApi) (W := 1088)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Encrypt
      verified := Proof.TripleDes.Arm.cfb8Encrypt_framed }
    Impl.TripleDes.Arm.Fn.modeWords []
    Scrub.cfb8EncryptOut
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_cfb8_decrypt`. -/
theorem cfb8Decrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cfb8Decrypt (Spec.TripleDes.cfb8DecryptContract Arm.abi 1088) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfb8DecryptApi) (W := 1088)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Decrypt
      verified := Proof.TripleDes.Arm.cfb8Decrypt_framed }
    Impl.TripleDes.Arm.Fn.modeWords []
    Scrub.cfb8DecryptOut
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_ofb`. -/
theorem ofb : VerifiedScrubbed target Impl.TripleDes.Arm.Fn.ofb (Spec.TripleDes.ofbContract Arm.abi 1088) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ofbApi) (W := 1088)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.ofb
      verified := Proof.TripleDes.Arm.ofb_framed }
    Impl.TripleDes.Arm.Fn.modeWords []
    Scrub.ofbOut
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_ofb_final`. -/
theorem ofbFinal :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.ofbFinal (Spec.TripleDes.ofbFinalContract Arm.abi 1088) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ofbFinalApi) (W := 1088)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.ofbFinal
      verified := Proof.TripleDes.Arm.ofbFinal_framed }
    Impl.TripleDes.Arm.Fn.modeWords []
    Scrub.ofbFinalOut
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

end VG.Proof.TripleDes.Arm.Fn
