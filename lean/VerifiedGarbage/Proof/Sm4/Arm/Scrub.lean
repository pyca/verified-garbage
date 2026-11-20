module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
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

/-!
# SM4's key expansion, ECB and modes on ARMv7, as emitted

Each function is its code with its cleanup (`Impl.Sm4.Arm.Fn`): the stack
its contract reserves zeroed, and the registers a callee may change set to
constants. `Fn` below has the theorem of each: it meets its contract in
constant time and returns without secret residue (`VerifiedScrubbed`), from
`Arm.Scrub.verifiedScrubbedF`, which is what its registration binds.

What the cleanup needs of the code (`CodeOk`: its frames within that stack,
and no indirect call) is evaluated by `lit_decide`, and the postconditions
read the memory on return only within their buffers (`Arm.Scrub.PostOut`,
from the lemmas of `Proof/Sm4/Scratch.lean` and its neighbours, which
RISC-V's uses too). ECB's contract reserves 1480 bytes and the final CFB and
OFB functions' 1560, which are no frame size of the model (`FrameOk`): they
are proven with 1488 and 1568 (`Arm.Scrub.Verified.stack_le`).
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

/-! ## The code: its frames, and no indirect call -/

theorem expandKey_ok : CodeOk (withRegScratchWiped 1456 .r2 364 Impl.Sm4.Arm.expandKey) 1456 := by
  lit_decide

theorem ecb_ok (d : Impl.Sm4.Arm.Dir) : CodeOk (Impl.Sm4.Arm.ecbCall d) 1488 := by
  cases d <;> lit_decide

theorem cbcEncrypt_ok : CodeOk (withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.SerialCbc.encrypt) 1520 := by
  lit_decide

theorem cbcDecrypt_ok : CodeOk (withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.BatchCbc.decrypt) 1520 := by
  lit_decide

theorem cfbEncrypt_ok : CodeOk (withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.SerialCfb.encrypt) 1520 := by
  lit_decide

theorem cfbDecrypt_ok : CodeOk (withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.BatchCfb.decrypt) 1520 := by
  lit_decide

theorem ofb_ok : CodeOk (withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.SerialOfb.crypt) 1520 := by
  lit_decide

theorem ctr_ok : CodeOk Impl.Sm4.Arm.ctrFramed 1520 := by
  lit_decide

theorem cfbEncryptFinal_ok :
    CodeOk (withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cfbEncryptFinal) 1568 := by
  lit_decide

theorem cfbDecryptFinal_ok :
    CodeOk (withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cfbDecryptFinal) 1568 := by
  lit_decide

theorem ofbFinal_ok : CodeOk (withStackScratchWiped 80 0 18 Impl.Sm4.Arm.ofbFinal) 1568 := by
  lit_decide

theorem ctrFinal_ok : CodeOk (withStackScratchWiped 64 0 14 Impl.Sm4.Arm.ctrFinal) 1584 := by
  lit_decide

end VG.Proof.Sm4.Arm.Scrub

namespace VG.Proof.Sm4.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Impl.StackScratch.Arm

/-- `vg_sm4_expand_key`. -/
theorem expandKey :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.expandKey (Spec.Sm4.expandKeyContract abi 1456) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.expandKeyApi)
    { code := withRegScratchWiped 1456 .r2 364 Impl.Sm4.Arm.expandKey
      verified := Proof.Sm4.Arm.expandKey_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.expandKeyPostOut_local _))
    (scrubSideF_of Scrub.expandKey_ok (by decide) _)

/-- `vg_sm4_ecb_encrypt`. -/
theorem ecbEncrypt :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.ecbEncrypt (Spec.Sm4.ecbContract abi .encrypt 1488) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.ecbEncryptApi)
    { code := Impl.Sm4.Arm.ecbCall .encrypt, verified := Scrub.ecb_verified .encrypt }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ecbPostOut_local _ .encrypt))
    (scrubSideF_of (Scrub.ecb_ok .encrypt) (by decide) _)

/-- `vg_sm4_ecb_decrypt`. -/
theorem ecbDecrypt :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.ecbDecrypt (Spec.Sm4.ecbContract abi .decrypt 1488) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.ecbDecryptApi)
    { code := Impl.Sm4.Arm.ecbCall .decrypt, verified := Scrub.ecb_verified .decrypt }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ecbPostOut_local _ .decrypt))
    (scrubSideF_of (Scrub.ecb_ok .decrypt) (by decide) _)

/-- `vg_sm4_cbc_encrypt_chained`. -/
theorem cbcEncryptChained :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cbcEncryptChained
      (Spec.Sm4.cbcEncryptChainedContract abi 1520) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.cbcEncryptChainedApi)
    { code := withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.SerialCbc.encrypt
      verified := Proof.Sm4.Arm.SerialCbcVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cbcEncChainedPostOut_local _))
    (scrubSideF_of Scrub.cbcEncrypt_ok (by decide) _)

/-- `vg_sm4_cbc_decrypt_chained`. -/
theorem cbcDecryptChained :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cbcDecryptChained
      (Spec.Sm4.cbcDecryptChainedContract abi 1520) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.cbcDecryptChainedApi)
    { code := withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.BatchCbc.decrypt
      verified := Proof.Sm4.Arm.CbcBatchVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cbcDecChainedPostOut_local _))
    (scrubSideF_of Scrub.cbcDecrypt_ok (by decide) _)

/-- `vg_sm4_cfb128_encrypt`. -/
theorem cfbEncrypt :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cfbEncrypt (Spec.Sm4.cfbEncryptContract abi 1520) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.cfbEncryptApi)
    { code := withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.SerialCfb.encrypt
      verified := Proof.Sm4.Arm.SerialCfbVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cfbEncPostOut_local _))
    (scrubSideF_of Scrub.cfbEncrypt_ok (by decide) _)

/-- `vg_sm4_cfb128_decrypt`. -/
theorem cfbDecrypt :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cfbDecrypt (Spec.Sm4.cfbDecryptContract abi 1520) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.cfbDecryptApi)
    { code := withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.BatchCfb.decrypt
      verified := Proof.Sm4.Arm.CfbBatchVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cfbDecPostOut_local _))
    (scrubSideF_of Scrub.cfbDecrypt_ok (by decide) _)

/-- `vg_sm4_cfb128_encrypt_final`. -/
theorem cfbEncryptFinal :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cfbEncryptFinal (Spec.Sm4.cfbEncryptFinalContract abi 1568) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.cfbEncryptFinalApi)
    { code := withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cfbEncryptFinal
      verified := Verified.stack_le (by decide) Proof.Sm4.Arm.cfbEncryptFinal_framed Scrub.cfbEncryptFinalSat }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _))
    (scrubSideF_of Scrub.cfbEncryptFinal_ok (by decide) _)

/-- `vg_sm4_cfb128_decrypt_final`. -/
theorem cfbDecryptFinal :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cfbDecryptFinal (Spec.Sm4.cfbDecryptFinalContract abi 1568) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.cfbDecryptFinalApi)
    { code := withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cfbDecryptFinal
      verified := Verified.stack_le (by decide) Proof.Sm4.Arm.cfbDecryptFinal_framed Scrub.cfbDecryptFinalSat }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _))
    (scrubSideF_of Scrub.cfbDecryptFinal_ok (by decide) _)

/-- `vg_sm4_ctr`. -/
theorem ctr : VerifiedScrubbed target Impl.Sm4.Arm.Fn.ctr (Spec.Sm4.ctrContract abi 1520) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.ctrApi)
    { code := Impl.Sm4.Arm.ctrFramed, verified := Proof.Sm4.Arm.BatchVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ctrPostOut_local _))
    (scrubSideF_of Scrub.ctr_ok (by decide) _)

/-- `vg_sm4_ctr_final`. -/
theorem ctrFinal :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.ctrFinal (Spec.Sm4.ctrFinalContract abi 1584) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.ctrFinalApi)
    { code := withStackScratchWiped 64 0 14 Impl.Sm4.Arm.ctrFinal
      verified := Proof.Sm4.Arm.CtrFinal.ctrFinal_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ctrFinalPostOut_local _))
    (scrubSideF_of Scrub.ctrFinal_ok (by decide) _)

/-- `vg_sm4_ofb`. -/
theorem ofb : VerifiedScrubbed target Impl.Sm4.Arm.Fn.ofb (Spec.Sm4.ofbContract abi 1520) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.ofbApi)
    { code := withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.SerialOfb.crypt
      verified := Proof.Sm4.Arm.SerialOfbVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ofbPostOut_local _))
    (scrubSideF_of Scrub.ofb_ok (by decide) _)

/-- `vg_sm4_ofb_final`. -/
theorem ofbFinal :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.ofbFinal (Spec.Sm4.ofbFinalContract abi 1568) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.ofbFinalApi)
    { code := withStackScratchWiped 80 0 18 Impl.Sm4.Arm.ofbFinal
      verified := Verified.stack_le (by decide) Proof.Sm4.Arm.ofbFinal_framed Scrub.ofbFinalSat }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _))
    (scrubSideF_of Scrub.ofbFinal_ok (by decide) _)

end VG.Proof.Sm4.Arm.Fn
