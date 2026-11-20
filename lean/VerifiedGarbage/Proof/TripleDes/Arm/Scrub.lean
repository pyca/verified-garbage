module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
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

/-!
# Triple DES on ARMv7, without secret residue

Every public function of Triple DES on ARMv7 keeps its working space in a
frame: key expansion's 512 bytes and ECB's 1024 (`withRegScratchWiped`),
the batched CBC and CFB64 decryption's 1040, and the modes one block at a
time 64 bytes of their own around ECB's 1024 (`withStackScratchWiped`).
None makes an indirect call, and their postconditions read the memory on
return only within their buffers (`Arm.Scrub.PostOut`, from the lemmas of
`Proof/TripleDes/Scratch.lean`, `CbcScratch.lean`, `FbScratch.lean` and
`Proof/Modes/CfbFinalScratch.lean` that x86-64 uses too). Each is emitted
followed by a wipe of the stack its contract reserves and by instructions
that set the registers a callee may change, but the result, and the flags
to constants (`Impl.TripleDes.Arm.Fn`), and `Fn` below states
that each returns without secret residue (`Arm.Scrub.verifiedScrubbedF`),
which is what its registration binds.

The modes call ECB's code as it is verified, without the wipe, under names
of their own (`vg_triple_des_ecb_encrypt_entry`, `Impl.TripleDes.Arm.ecbCore`),
which the emitter writes as internal functions: their own wipe covers the
frame of that call.
-/

@[expose] public section

namespace VG.Proof.TripleDes.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Modes.Arm

/-! ## The postconditions -/

theorem expandKeyOut : PostOut (Spec.TripleDes.expandKeyContract Arm.abi 512) (Spec.TripleDes.expandKeySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.expandKeyPostOut_local _)

theorem ecbOut (d : Spec.TripleDes.Direction) :
    PostOut (Spec.TripleDes.ecbContract Arm.abi d 1024) (Spec.TripleDes.ecbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.ecbPostOut_local _ d)

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

/-! ## The code: its frames, and no indirect call -/

theorem frameOk_512 : FrameOk 512 := by decide
theorem frameOk_1024 : FrameOk 1024 := by decide
theorem frameOk_1040 : FrameOk 1040 := by decide
theorem frameOk_1088 : FrameOk 1088 := by decide

theorem expandKey_code : armStack Impl.TripleDes.Arm.Key.expandKey = 0 ∧
    noIcall Impl.TripleDes.Arm.Key.expandKey = true := by lit_decide

theorem encrypt_code : armStack Impl.TripleDes.Arm.Bitslice.encrypt = 0 ∧
    noIcall Impl.TripleDes.Arm.Bitslice.encrypt = true := by lit_decide

theorem decrypt_code : armStack Impl.TripleDes.Arm.Bitslice.decrypt = 0 ∧
    noIcall Impl.TripleDes.Arm.Bitslice.decrypt = true := by lit_decide

theorem cbcDecrypt_code : armStack Impl.TripleDes.Arm.Wide.cbcDecrypt = 0 ∧
    noIcall Impl.TripleDes.Arm.Wide.cbcDecrypt = true := by lit_decide

theorem cfbDecrypt_code : armStack Impl.TripleDes.Arm.Wide.cfbDecrypt = 0 ∧
    noIcall Impl.TripleDes.Arm.Wide.cfbDecrypt = true := by lit_decide

theorem ecbCode_scrub (d : Spec.TripleDes.Direction) :
    CodeOk (Impl.TripleDes.Arm.ecbCode d) 1024 := by
  cases d
  · exact withRegScratchWiped_scrubArm (n := 0) ⟨Nat.le_of_eq encrypt_code.1, encrypt_code.2⟩
  · exact withRegScratchWiped_scrubArm (n := 0) ⟨Nat.le_of_eq decrypt_code.1, decrypt_code.2⟩

/-- ECB's code, as the modes call it. -/
theorem ecbCore_scrub (d : Spec.TripleDes.Direction) :
    armStack (Impl.TripleDes.Arm.ecbCore d).code + callExtraArm (Impl.TripleDes.Arm.ecbCore d) ≤ 1024 ∧
      noIcall (Impl.TripleDes.Arm.ecbCore d).code = true := by
  simpa only [callExtraArm, Impl.TripleDes.Arm.ecbCore, ite_true, Nat.add_zero] using ecbCode_scrub d

/-- A mode one block at a time, in its 64-byte scratch frame. -/
theorem seq_scrub (m : Impl.Modes.Arm.Mode) :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 ((Impl.TripleDes.Arm.ecbCore .encrypt).seq m)) ≤ 1088 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14
        ((Impl.TripleDes.Arm.ecbCore .encrypt).seq m)) = true :=
  withStackScratchWiped_scrubArm (seq_scrubArm (ecbCore_scrub .encrypt) m)

/-- A mode over a message's last piece, in its 64-byte scratch frame. -/
theorem seqFinal_scrub (m : Impl.Modes.Arm.Mode) :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14
      ((Impl.TripleDes.Arm.ecbCore .encrypt).seqFinal m)) ≤ 1088 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14
        ((Impl.TripleDes.Arm.ecbCore .encrypt).seqFinal m)) = true :=
  withStackScratchWiped_scrubArm (seqFinal_scrubArm (ecbCore_scrub .encrypt) m)

theorem cbcEncryptChained_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cbcEncryptChained) 1088 :=
  seq_scrub Impl.Modes.Arm.cbcEncChained

theorem cfbEncrypt_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbEncrypt) 1088 :=
  seq_scrub Impl.Modes.Arm.cfbEnc

theorem cfbEncryptFinal_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbEncryptFinal) 1088 :=
  seqFinal_scrub Impl.Modes.Arm.cfbEnc

theorem cfbDecryptFinal_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbDecryptFinal) 1088 :=
  seqFinal_scrub Impl.Modes.Arm.cfbDecF

theorem cfb8Encrypt_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Encrypt) 1088 :=
  seq_scrub Impl.Modes.Arm.cfb8Enc

theorem cfb8Decrypt_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Decrypt) 1088 :=
  seq_scrub Impl.Modes.Arm.cfb8Dec

theorem ofb_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.ofb) 1088 :=
  seq_scrub Impl.Modes.Arm.ofb

theorem ofbFinal_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.ofbFinal) 1088 :=
  seqFinal_scrub Impl.Modes.Arm.ofb

theorem wide_scrub {c : Prog isa} (hc : armStack c = 0 ∧ noIcall c = true) :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 1040 0 256 c) 1040 :=
  withStackScratchWiped_scrubArm (n := 0) ⟨Nat.le_of_eq hc.1, hc.2⟩

end VG.Proof.TripleDes.Arm.Scrub

namespace VG.Proof.TripleDes.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Modes.Arm

/-- `vg_triple_des_expand_key`. -/
theorem expandKey :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.expandKey (Spec.TripleDes.expandKeyContract Arm.abi 512) 0 :=
  verifiedScrubbedF (api := Spec.TripleDes.expandKeyApi)
    { code := Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.TripleDes.Arm.Key.expandKey
      verified := Proof.TripleDes.Arm.expandKey_framed }
    Scrub.expandKeyOut
    (scrubSideF_of (withRegScratchWiped_scrubArm (n := 0)
      ⟨Nat.le_of_eq Scrub.expandKey_code.1, Scrub.expandKey_code.2⟩) Scrub.frameOk_512 _)

/-- `vg_triple_des_ecb_encrypt`. -/
theorem ecbEncrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.ecbEncrypt (Spec.TripleDes.ecbContract Arm.abi .encrypt 1024) 0 :=
  verifiedScrubbedF (api := Spec.TripleDes.ecbEncryptApi)
    { code := Impl.TripleDes.Arm.ecbCode .encrypt
      verified := Proof.TripleDes.Arm.ecb_framed Proof.TripleDes.Arm.Bitsliced.encrypt_verified }
    (Scrub.ecbOut .encrypt) (scrubSideF_of (Scrub.ecbCode_scrub .encrypt) Scrub.frameOk_1024 _)

/-- `vg_triple_des_ecb_decrypt`. -/
theorem ecbDecrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.ecbDecrypt (Spec.TripleDes.ecbContract Arm.abi .decrypt 1024) 0 :=
  verifiedScrubbedF (api := Spec.TripleDes.ecbDecryptApi)
    { code := Impl.TripleDes.Arm.ecbCode .decrypt
      verified := Proof.TripleDes.Arm.ecb_framed Proof.TripleDes.Arm.Bitsliced.decrypt_verified }
    (Scrub.ecbOut .decrypt) (scrubSideF_of (Scrub.ecbCode_scrub .decrypt) Scrub.frameOk_1024 _)

/-- `vg_triple_des_cbc_encrypt_chained`. -/
theorem cbcEncrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cbcEncrypt (Spec.TripleDes.cbcEncryptChainedContract Arm.abi 1088) 0 :=
  verifiedScrubbedF (api := Spec.TripleDes.cbcEncryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cbcEncryptChained
      verified := Proof.TripleDes.Arm.cbcEncryptChained_framed }
    Scrub.cbcEncryptOut (scrubSideF_of Scrub.cbcEncryptChained_scrub Scrub.frameOk_1088 _)

/-- `vg_triple_des_cbc_decrypt_chained`. -/
theorem cbcDecrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cbcDecrypt (Spec.TripleDes.cbcDecryptChainedContract Arm.abi 1040) 0 :=
  verifiedScrubbedF (api := Spec.TripleDes.cbcDecryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 1040 0 256 Impl.TripleDes.Arm.Wide.cbcDecrypt
      verified := Proof.TripleDes.Arm.Bitsliced.cbcDecrypt_framed }
    Scrub.cbcDecryptOut (scrubSideF_of (Scrub.wide_scrub Scrub.cbcDecrypt_code) Scrub.frameOk_1040 _)

/-- `vg_triple_des_cfb64_encrypt`. -/
theorem cfbEncrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cfbEncrypt (Spec.TripleDes.cfbEncryptContract Arm.abi 1088) 0 :=
  verifiedScrubbedF (api := Spec.TripleDes.cfbEncryptApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbEncrypt
      verified := Proof.TripleDes.Arm.cfbEncrypt_framed }
    Scrub.cfbEncryptOut (scrubSideF_of Scrub.cfbEncrypt_scrub Scrub.frameOk_1088 _)

/-- `vg_triple_des_cfb64_decrypt`. -/
theorem cfbDecrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cfbDecrypt (Spec.TripleDes.cfbDecryptContract Arm.abi 1040) 0 :=
  verifiedScrubbedF (api := Spec.TripleDes.cfbDecryptApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 1040 0 256 Impl.TripleDes.Arm.Wide.cfbDecrypt
      verified := Proof.TripleDes.Arm.Bitsliced.cfbDecrypt_framed }
    Scrub.cfbDecryptOut (scrubSideF_of (Scrub.wide_scrub Scrub.cfbDecrypt_code) Scrub.frameOk_1040 _)

/-- `vg_triple_des_cfb64_encrypt_final`. -/
theorem cfbEncryptFinal :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cfbEncryptFinal (Spec.TripleDes.cfbEncryptFinalContract Arm.abi 1088) 0 :=
  verifiedScrubbedF (api := Spec.TripleDes.cfbEncryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbEncryptFinal
      verified := Proof.TripleDes.Arm.cfbEncryptFinal_framed }
    Scrub.cfbEncryptFinalOut (scrubSideF_of Scrub.cfbEncryptFinal_scrub Scrub.frameOk_1088 _)

/-- `vg_triple_des_cfb64_decrypt_final`. -/
theorem cfbDecryptFinal :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cfbDecryptFinal (Spec.TripleDes.cfbDecryptFinalContract Arm.abi 1088) 0 :=
  verifiedScrubbedF (api := Spec.TripleDes.cfbDecryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbDecryptFinal
      verified := Proof.TripleDes.Arm.cfbDecryptFinal_framed }
    Scrub.cfbDecryptFinalOut (scrubSideF_of Scrub.cfbDecryptFinal_scrub Scrub.frameOk_1088 _)

/-- `vg_triple_des_cfb8_encrypt`. -/
theorem cfb8Encrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cfb8Encrypt (Spec.TripleDes.cfb8EncryptContract Arm.abi 1088) 0 :=
  verifiedScrubbedF (api := Spec.TripleDes.cfb8EncryptApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Encrypt
      verified := Proof.TripleDes.Arm.cfb8Encrypt_framed }
    Scrub.cfb8EncryptOut (scrubSideF_of Scrub.cfb8Encrypt_scrub Scrub.frameOk_1088 _)

/-- `vg_triple_des_cfb8_decrypt`. -/
theorem cfb8Decrypt :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.cfb8Decrypt (Spec.TripleDes.cfb8DecryptContract Arm.abi 1088) 0 :=
  verifiedScrubbedF (api := Spec.TripleDes.cfb8DecryptApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Decrypt
      verified := Proof.TripleDes.Arm.cfb8Decrypt_framed }
    Scrub.cfb8DecryptOut (scrubSideF_of Scrub.cfb8Decrypt_scrub Scrub.frameOk_1088 _)

/-- `vg_triple_des_ofb`. -/
theorem ofb : VerifiedScrubbed target Impl.TripleDes.Arm.Fn.ofb (Spec.TripleDes.ofbContract Arm.abi 1088) 0 :=
  verifiedScrubbedF (api := Spec.TripleDes.ofbApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.ofb
      verified := Proof.TripleDes.Arm.ofb_framed }
    Scrub.ofbOut (scrubSideF_of Scrub.ofb_scrub Scrub.frameOk_1088 _)

/-- `vg_triple_des_ofb_final`. -/
theorem ofbFinal :
    VerifiedScrubbed target Impl.TripleDes.Arm.Fn.ofbFinal (Spec.TripleDes.ofbFinalContract Arm.abi 1088) 0 :=
  verifiedScrubbedF (api := Spec.TripleDes.ofbFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.ofbFinal
      verified := Proof.TripleDes.Arm.ofbFinal_framed }
    Scrub.ofbFinalOut (scrubSideF_of Scrub.ofbFinal_scrub Scrub.frameOk_1088 _)

end VG.Proof.TripleDes.Arm.Fn
