module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
public import VerifiedGarbage.Impl.Sm4.Arm.Fn
public import VerifiedGarbage.Proof.Sm4.Arm.KeyVerified
public import VerifiedGarbage.Proof.Sm4.Arm.EcbCall
public import VerifiedGarbage.Proof.Sm4.Arm.SerialCbcVerified
public import VerifiedGarbage.Proof.Sm4.Arm.CbcBatchVerified
public import VerifiedGarbage.Proof.Sm4.Arm.SerialCfbVerified
public import VerifiedGarbage.Proof.Sm4.Arm.CfbBatchVerified
public import VerifiedGarbage.Proof.Sm4.Arm.SerialOfbVerified
public import VerifiedGarbage.Proof.Sm4.Arm.BatchVerified
public import VerifiedGarbage.Proof.Sm4.Arm.CtrFinal
public import VerifiedGarbage.Proof.Sm4.Arm.FbFinalVerified
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Sm4.CbcScratch
import VerifiedGarbage.Proof.Sm4.FbScratch
import VerifiedGarbage.Proof.Sm4.CtrFinal
import VerifiedGarbage.Proof.Sm4.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
meta import VerifiedGarbage.Impl.Sm4.Arm.Fn
meta import VerifiedGarbage.Proof.Sm4.Arm.KeyVerified
meta import VerifiedGarbage.Proof.Sm4.Arm.EcbCall
meta import VerifiedGarbage.Proof.Sm4.Arm.SerialCbcVerified
meta import VerifiedGarbage.Proof.Sm4.Arm.CbcBatchVerified
meta import VerifiedGarbage.Proof.Sm4.Arm.SerialCfbVerified
meta import VerifiedGarbage.Proof.Sm4.Arm.CfbBatchVerified
meta import VerifiedGarbage.Proof.Sm4.Arm.SerialOfbVerified
meta import VerifiedGarbage.Proof.Sm4.Arm.BatchVerified
meta import VerifiedGarbage.Proof.Sm4.Arm.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.Arm.FbFinalVerified
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Sm4.CbcScratch
meta import VerifiedGarbage.Proof.Sm4.FbScratch
meta import VerifiedGarbage.Proof.Sm4.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# SM4's key expansion, ECB and modes on ARMv7, as emitted

Each function is its code with its cleanup (`Impl.Sm4.Arm.Fn`): of the stack
its contract reserves, only the words that the residue analysis finds may
differ between two runs zeroed (`Impl.Scrub.Arm.scrubSel`), and the
registers a callee may change set to constants. `Fn` below has the theorem of
each: it meets its contract in constant time and returns without secret
residue (`VerifiedScrubbed`), from `Arm.Scrub.verifiedScrubbedSel`, whose
analysis (`Arm.rtaint`) the kernel evaluates here (`taint_decide_ct`), which
is what its registration binds.

The postconditions read the memory on return only within their buffers
(`Arm.Scrub.PostOut`, from the lemmas of `Proof/Sm4/Scratch.lean` and its
neighbours, which RISC-V's uses too). ECB's contract reserves 1480 bytes and
the final CFB and OFB functions' 1560, which are no frame size of the model
(`FrameOk`): they are proven with 1488 and 1568
(`Arm.Scrub.Verified.stack_le`).
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Impl.StackScratch.Arm

/-! ## The stack, rounded up to a frame of the model -/

theorem ecbSat (d : Impl.Sm4.Arm.Dir) :
    ∃ s, (Spec.Sm4.ecbContract Arm.abi (specDirArm d) 1488).pre s := by
  cases d <;>
  sig_implies_sat [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, specDirArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr] [ecbCallSat] using ecbCallSat

theorem ecb_verified (d : Impl.Sm4.Arm.Dir) :
    Verified Arm.target (Impl.Sm4.Arm.ecbCall d) (Spec.Sm4.ecbContract Arm.abi (specDirArm d) 1488) :=
  Verified.stack_le (by decide) (ecbCall_verified d) (ecbSat d)

theorem cfbEncryptFinalSat : ∃ s, (Spec.Sm4.cfbEncryptFinalContract Arm.abi 1568).pre s := by
  implies_sat [Spec.Sm4.cfbEncryptFinalContract, Spec.Sm4.cfbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 1

theorem cfbDecryptFinalSat : ∃ s, (Spec.Sm4.cfbDecryptFinalContract Arm.abi 1568).pre s := by
  implies_sat [Spec.Sm4.cfbDecryptFinalContract, Spec.Sm4.cfbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 1

theorem ofbFinalSat : ∃ s, (Spec.Sm4.ofbFinalContract Arm.abi 1568).pre s := by
  implies_sat [Spec.Sm4.ofbFinalContract, Spec.Sm4.ofbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 1

/-! ## The stack the functions zeroed in a loop use

The frames of the key expansion and of the modes over whole blocks, which
`scrubAll` zeroes (`Arm.Scrub.CodeOk`). -/

theorem expandKey_code : CodeOk (withRegScratch 1456 .r2 Impl.Sm4.Arm.expandKey) 1456 := by lit_decide
theorem cbcEncryptChained_code : CodeOk (withStackScratch 1520 0 Impl.Sm4.Arm.SerialCbc.encrypt) 1520 := by
  lit_decide
theorem cbcDecryptChained_code : CodeOk (withStackScratch 1520 0 Impl.Sm4.Arm.BatchCbc.decrypt) 1520 := by
  lit_decide
theorem cfbEncrypt_code : CodeOk (withStackScratch 1520 0 Impl.Sm4.Arm.SerialCfb.encrypt) 1520 := by lit_decide
theorem cfbDecrypt_code : CodeOk (withStackScratch 1520 0 Impl.Sm4.Arm.BatchCfb.decrypt) 1520 := by lit_decide
theorem ctr_code : CodeOk (withStackScratch 1520 0 Impl.Sm4.Arm.BatchCtr.ctr) 1520 := by lit_decide
theorem ofb_code : CodeOk (withStackScratch 1520 0 Impl.Sm4.Arm.SerialOfb.crypt) 1520 := by lit_decide

end VG.Proof.Sm4.Arm.Scrub

namespace VG.Proof.Sm4.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Impl.StackScratch.Arm

/-- `vg_sm4_expand_key`. -/
theorem expandKey :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.expandKey (Spec.Sm4.expandKeyContract abi 1456) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.expandKeyApi)
    { code := withRegScratch 1456 .r2 Impl.Sm4.Arm.expandKey
      verified := Proof.Sm4.Arm.expandKey_framedU }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.expandKeyPostOut_local _))
    (scrubSideF_of Scrub.expandKey_code (by decide) _)

/-- `vg_sm4_ecb_encrypt`. -/
theorem ecbEncrypt :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.ecbEncrypt (Spec.Sm4.ecbContract abi .encrypt 1488) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ecbEncryptApi) (W := 1488)
    { code := Impl.Sm4.Arm.ecbCall .encrypt, verified := Scrub.ecb_verified .encrypt }
    Impl.Sm4.Arm.Fn.ecbWords []
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ecbPostOut_local _ .encrypt))
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_ecb_decrypt`. -/
theorem ecbDecrypt :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.ecbDecrypt (Spec.Sm4.ecbContract abi .decrypt 1488) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ecbDecryptApi) (W := 1488)
    { code := Impl.Sm4.Arm.ecbCall .decrypt, verified := Scrub.ecb_verified .decrypt }
    Impl.Sm4.Arm.Fn.ecbWords []
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ecbPostOut_local _ .decrypt))
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_cbc_encrypt_chained`. -/
theorem cbcEncryptChained :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cbcEncryptChained
      (Spec.Sm4.cbcEncryptChainedContract abi 1520) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.cbcEncryptChainedApi)
    { code := withStackScratch 1520 0 Impl.Sm4.Arm.SerialCbc.encrypt
      verified := Proof.Sm4.Arm.SerialCbcVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cbcEncChainedPostOut_local _))
    (scrubSideF_of Scrub.cbcEncryptChained_code (by decide) _)

/-- `vg_sm4_cbc_decrypt_chained`. -/
theorem cbcDecryptChained :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cbcDecryptChained
      (Spec.Sm4.cbcDecryptChainedContract abi 1520) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.cbcDecryptChainedApi)
    { code := withStackScratch 1520 0 Impl.Sm4.Arm.BatchCbc.decrypt
      verified := Proof.Sm4.Arm.CbcBatchVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cbcDecChainedPostOut_local _))
    (scrubSideF_of Scrub.cbcDecryptChained_code (by decide) _)

/-- `vg_sm4_cfb128_encrypt`. -/
theorem cfbEncrypt :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cfbEncrypt (Spec.Sm4.cfbEncryptContract abi 1520) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.cfbEncryptApi)
    { code := withStackScratch 1520 0 Impl.Sm4.Arm.SerialCfb.encrypt
      verified := Proof.Sm4.Arm.SerialCfbVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cfbEncPostOut_local _))
    (scrubSideF_of Scrub.cfbEncrypt_code (by decide) _)

/-- `vg_sm4_cfb128_decrypt`. -/
theorem cfbDecrypt :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cfbDecrypt (Spec.Sm4.cfbDecryptContract abi 1520) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.cfbDecryptApi)
    { code := withStackScratch 1520 0 Impl.Sm4.Arm.BatchCfb.decrypt
      verified := Proof.Sm4.Arm.CfbBatchVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cfbDecPostOut_local _))
    (scrubSideF_of Scrub.cfbDecrypt_code (by decide) _)

/-- `vg_sm4_cfb128_encrypt_final`. -/
theorem cfbEncryptFinal :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cfbEncryptFinal (Spec.Sm4.cfbEncryptFinalContract abi 1568) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cfbEncryptFinalApi) (W := 1568)
    { code := withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cfbEncryptFinal
      verified := Verified.stack_le (by decide) Proof.Sm4.Arm.cfbEncryptFinal_framed Scrub.cfbEncryptFinalSat }
    Impl.Sm4.Arm.Fn.finalWords []
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _))
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_cfb128_decrypt_final`. -/
theorem cfbDecryptFinal :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cfbDecryptFinal (Spec.Sm4.cfbDecryptFinalContract abi 1568) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cfbDecryptFinalApi) (W := 1568)
    { code := withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cfbDecryptFinal
      verified := Verified.stack_le (by decide) Proof.Sm4.Arm.cfbDecryptFinal_framed Scrub.cfbDecryptFinalSat }
    Impl.Sm4.Arm.Fn.finalWords []
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _))
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_ctr`. -/
theorem ctr : VerifiedScrubbed target Impl.Sm4.Arm.Fn.ctr (Spec.Sm4.ctrContract abi 1520) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.ctrApi)
    { code := withStackScratch 1520 0 Impl.Sm4.Arm.BatchCtr.ctr
      verified := Proof.Sm4.Arm.BatchVerified.framedU }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ctrPostOut_local _))
    (scrubSideF_of Scrub.ctr_code (by decide) _)

/-- `vg_sm4_ctr_final`. -/
theorem ctrFinal :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.ctrFinal (Spec.Sm4.ctrFinalContract abi 1584) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ctrFinalApi) (W := 1584)
    { code := withStackScratchWiped 64 0 14 Impl.Sm4.Arm.ctrFinal
      verified := Proof.Sm4.Arm.CtrFinal.ctrFinal_framed }
    Impl.Sm4.Arm.Fn.ctrFinalWords []
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ctrFinalPostOut_local _))
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_ofb`. -/
theorem ofb : VerifiedScrubbed target Impl.Sm4.Arm.Fn.ofb (Spec.Sm4.ofbContract abi 1520) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.ofbApi)
    { code := withStackScratch 1520 0 Impl.Sm4.Arm.SerialOfb.crypt
      verified := Proof.Sm4.Arm.SerialOfbVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ofbPostOut_local _))
    (scrubSideF_of Scrub.ofb_code (by decide) _)

/-- `vg_sm4_ofb_final`. -/
theorem ofbFinal :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.ofbFinal (Spec.Sm4.ofbFinalContract abi 1568) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ofbFinalApi) (W := 1568)
    { code := withStackScratchWiped 80 0 18 Impl.Sm4.Arm.ofbFinal
      verified := Verified.stack_le (by decide) Proof.Sm4.Arm.ofbFinal_framed Scrub.ofbFinalSat }
    Impl.Sm4.Arm.Fn.finalWords []
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _))
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

end VG.Proof.Sm4.Arm.Fn
