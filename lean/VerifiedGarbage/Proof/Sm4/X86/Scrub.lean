module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Sm4.X86.Fn
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.CfbFinal
public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Sm4.OfbFinal
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Spec.Sm4.CtrFinal
public import VerifiedGarbage.Proof.Sm4.X86.KeyVerified
public import VerifiedGarbage.Proof.Sm4.X86.Verified
public import VerifiedGarbage.Proof.Sm4.X86.CbcVerified
public import VerifiedGarbage.Proof.Sm4.X86.FbVerified
public import VerifiedGarbage.Proof.Sm4.X86.FbFinalVerified
public import VerifiedGarbage.Proof.Sm4.X86.CtrVerified
public import VerifiedGarbage.Proof.Sm4.X86.CtrFinal
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Sm4.CbcScratch
import VerifiedGarbage.Proof.Sm4.FbScratch
import VerifiedGarbage.Proof.Sm4.CtrFinal
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.Sm4.X86.Lit
import VerifiedGarbage.Proof.Sm4.X86.CbcLit
import VerifiedGarbage.Proof.Sm4.X86.FbLit
import VerifiedGarbage.Proof.Sm4.X86.FbFinalLit
import VerifiedGarbage.Proof.Sm4.X86.CtrLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM4 on x86 (32-bit), without secret residue

Key expansion and SM4's ECB, CBC, CFB128, OFB and CTR functions, and the
final pieces of CFB128, OFB and CTR, run with their working space in a frame
on the stack, wiped before they return (`withStackScratchWiped`). As emitted
(`Impl.Sm4.X86.Fn`), each then zeroes the stack its contract reserves below
`esp` (its frame and the calls in it) and clears the registers a callee may
change, and returns without secret residue (`X86.Scrub.verifiedScrubbedF`),
given that its postcondition reads the memory on return only within the
buffers (`Proof/Sm4/Scratch.lean`, `CbcScratch.lean`, `FbScratch.lean`,
`CtrFinal.lean` and `Proof/Modes/CfbFinalScratch.lean`, for any pointer
width). What the cleanup needs of the code is one Boolean
(`X86.Scrub.scrubFSide`), proved by evaluating the code once
(`lit_decide`). `vg_sm4_ctr_final` calls `vg_sm4_ctr`'s code as an internal
function of its own, `vg_sm4_ctr_core` (`Impl.Sm4.X86.ctrFramed`), and
SM4-GCM `vg_sm4_expand_key`'s as `vg_sm4_expand_key_core`
(`Impl.Sm4Gcm.X86.keyFn`).
-/

@[expose] public section

namespace VG.Proof.Sm4.X86.Scrub

open VG.X86 VG.X86.Scrub
open Impl.StackScratch.X86 (withStackScratchWiped)

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) : PostOut (Spec.Sm4.expandKeyContract X86.abi stack) (Spec.Sm4.expandKeySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.expandKeyPostOut_local _)

theorem ecbOut (d : Spec.Sm4.Direction) (stack : Nat) :
    PostOut (Spec.Sm4.ecbContract X86.abi d stack) (Spec.Sm4.ecbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ecbPostOut_local _ d)

theorem cbcEncryptOut (stack : Nat) :
    PostOut (Spec.Sm4.cbcEncryptChainedContract X86.abi stack) (Spec.Sm4.cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cbcEncChainedPostOut_local _)

theorem cbcDecryptOut (stack : Nat) :
    PostOut (Spec.Sm4.cbcDecryptChainedContract X86.abi stack) (Spec.Sm4.cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cbcDecChainedPostOut_local _)

theorem cfbEncryptOut (stack : Nat) : PostOut (Spec.Sm4.cfbEncryptContract X86.abi stack) (Spec.Sm4.cfbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cfbEncPostOut_local _)

theorem cfbDecryptOut (stack : Nat) : PostOut (Spec.Sm4.cfbDecryptContract X86.abi stack) (Spec.Sm4.cfbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cfbDecPostOut_local _)

theorem cfbEncryptFinalOut (stack : Nat) :
    PostOut (Spec.Sm4.cfbEncryptFinalContract X86.abi stack) (Spec.Sm4.cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptFinalOut (stack : Nat) :
    PostOut (Spec.Sm4.cfbDecryptFinalContract X86.abi stack) (Spec.Sm4.cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem ofbOut (stack : Nat) : PostOut (Spec.Sm4.ofbContract X86.abi stack) (Spec.Sm4.ofbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ofbPostOut_local _)

theorem ofbFinalOut (stack : Nat) : PostOut (Spec.Sm4.ofbFinalContract X86.abi stack) (Spec.Sm4.ofbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

theorem ctrOut (stack : Nat) : PostOut (Spec.Sm4.ctrContract X86.abi stack) (Spec.Sm4.ctrSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ctrPostOut_local _)

theorem ctrFinalOut (stack : Nat) :
    PostOut (Spec.Sm4.ctrFinalContract X86.abi stack) (Spec.Sm4.ctrFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ctrFinalPostOut_local _)

/-! ## The functions as emitted -/

/-- `Spec.Sm4.expandKeyApi`'s function as emitted (`Impl.Sm4.X86.Fn.expandKey`) meets its contract
in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.expandKey (Spec.Sm4.expandKeyContract X86.abi 1448) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.expandKeyApi)
    { code := withStackScratchWiped 1448 2 358 Impl.Sm4.X86.expandKey
      verified := Proof.Sm4.X86.expandKey_framed }
    (expandKeyOut _)

/-- `Spec.Sm4.ecbEncryptApi`'s function as emitted (`Impl.Sm4.X86.Fn.ecbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.ecbEncrypt (Spec.Sm4.ecbContract X86.abi (Proof.Sm4.specDirX86 .encrypt) 1452) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.ecbEncryptApi)
    { code := withStackScratchWiped 1452 3 358 (Impl.Sm4.X86.ecb .encrypt)
      verified := Proof.Sm4.X86.ecb_framed .encrypt }
    (ecbOut _ _)

/-- `Spec.Sm4.ecbDecryptApi`'s function as emitted (`Impl.Sm4.X86.Fn.ecbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.ecbDecrypt (Spec.Sm4.ecbContract X86.abi (Proof.Sm4.specDirX86 .decrypt) 1452) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.ecbDecryptApi)
    { code := withStackScratchWiped 1452 3 358 (Impl.Sm4.X86.ecb .decrypt)
      verified := Proof.Sm4.X86.ecb_framed .decrypt }
    (ecbOut _ _)

/-- `Spec.Sm4.cbcEncryptChainedApi`'s function as emitted (`Impl.Sm4.X86.Fn.cbcEncryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.cbcEncryptChained (Spec.Sm4.cbcEncryptChainedContract X86.abi 1516) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.cbcEncryptChainedApi)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cbcEncryptChained
      verified := Proof.Sm4.X86.Cbc.cbcEncryptChained_framed }
    (cbcEncryptOut _)

/-- `Spec.Sm4.cbcDecryptChainedApi`'s function as emitted (`Impl.Sm4.X86.Fn.cbcDecryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.cbcDecryptChained (Spec.Sm4.cbcDecryptChainedContract X86.abi 1516) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.cbcDecryptChainedApi)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cbcDecryptChained
      verified := Proof.Sm4.X86.Cbc.cbcDecryptChained_framed }
    (cbcDecryptOut _)

/-- `Spec.Sm4.cfbEncryptApi`'s function as emitted (`Impl.Sm4.X86.Fn.cfbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.cfbEncrypt (Spec.Sm4.cfbEncryptContract X86.abi 1516) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.cfbEncryptApi)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbEncrypt
      verified := Proof.Sm4.X86.Fb.cfbEncrypt_framed }
    (cfbEncryptOut _)

/-- `Spec.Sm4.cfbDecryptApi`'s function as emitted (`Impl.Sm4.X86.Fn.cfbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.cfbDecrypt (Spec.Sm4.cfbDecryptContract X86.abi 1516) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.cfbDecryptApi)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbDecrypt
      verified := Proof.Sm4.X86.Fb.cfbDecrypt_framed }
    (cfbDecryptOut _)

/-- `Spec.Sm4.cfbEncryptFinalApi`'s function as emitted (`Impl.Sm4.X86.Fn.cfbEncryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.cfbEncryptFinal (Spec.Sm4.cfbEncryptFinalContract X86.abi 1516) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.cfbEncryptFinalApi)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbEncryptFinal
      verified := Proof.Sm4.X86.FbFinal.cfbEncryptFinal_framed }
    (cfbEncryptFinalOut _)

/-- `Spec.Sm4.cfbDecryptFinalApi`'s function as emitted (`Impl.Sm4.X86.Fn.cfbDecryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.cfbDecryptFinal (Spec.Sm4.cfbDecryptFinalContract X86.abi 1516) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.cfbDecryptFinalApi)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbDecryptFinal
      verified := Proof.Sm4.X86.FbFinal.cfbDecryptFinal_framed }
    (cfbDecryptFinalOut _)

/-- `Spec.Sm4.ofbApi`'s function as emitted (`Impl.Sm4.X86.Fn.ofb`) meets its contract
in constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.ofb (Spec.Sm4.ofbContract X86.abi 1516) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.ofbApi)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ofb
      verified := Proof.Sm4.X86.Fb.ofb_framed }
    (ofbOut _)

/-- `Spec.Sm4.ofbFinalApi`'s function as emitted (`Impl.Sm4.X86.Fn.ofbFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.ofbFinal (Spec.Sm4.ofbFinalContract X86.abi 1516) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.ofbFinalApi)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ofbFinal
      verified := Proof.Sm4.X86.FbFinal.ofbFinal_framed }
    (ofbFinalOut _)

/-- `Spec.Sm4.ctrApi`'s function as emitted (`Impl.Sm4.X86.Fn.ctr`) meets its contract
in constant time and returns without secret residue. -/
theorem ctr_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.ctr (Spec.Sm4.ctrContract X86.abi 1516) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.ctrApi)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ctr
      verified := Proof.Sm4.X86.Ctr.ctr_framed }
    (ctrOut _)

/-- `Spec.Sm4.ctrFinalApi`'s function as emitted (`Impl.Sm4.X86.Fn.ctrFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem ctrFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.ctrFinal (Spec.Sm4.ctrFinalContract X86.abi 1592) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.ctrFinalApi)
    { code := withStackScratchWiped 56 4 8 Impl.Sm4.X86.ctrFinal
      verified := Proof.Sm4.X86.CtrFinal.ctrFinal_framed
      spSafe := Proof.Sm4.X86.CtrFinal.ctrFinal_framed_spSafe }
    (ctrFinalOut _)

end VG.Proof.Sm4.X86.Scrub
