module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.X86.ScrubWiped
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
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Proof.Framework.X86.ScrubWiped
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Impl.Sm4.X86.Fn
meta import VerifiedGarbage.Spec.Sm4.Contract
meta import VerifiedGarbage.Spec.Sm4.Cbc
meta import VerifiedGarbage.Spec.Sm4.Cfb
meta import VerifiedGarbage.Spec.Sm4.CfbFinal
meta import VerifiedGarbage.Spec.Sm4.Ofb
meta import VerifiedGarbage.Spec.Sm4.OfbFinal
meta import VerifiedGarbage.Spec.Sm4.Ctr
meta import VerifiedGarbage.Spec.Sm4.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.X86.KeyVerified
meta import VerifiedGarbage.Proof.Sm4.X86.Verified
meta import VerifiedGarbage.Proof.Sm4.X86.CbcVerified
meta import VerifiedGarbage.Proof.Sm4.X86.FbVerified
meta import VerifiedGarbage.Proof.Sm4.X86.FbFinalVerified
meta import VerifiedGarbage.Proof.Sm4.X86.CtrVerified
meta import VerifiedGarbage.Proof.Sm4.X86.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Sm4.CbcScratch
meta import VerifiedGarbage.Proof.Sm4.FbScratch
meta import VerifiedGarbage.Proof.Sm4.CtrFinal
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Sm4.X86.Lit
meta import VerifiedGarbage.Proof.Sm4.X86.CbcLit
meta import VerifiedGarbage.Proof.Sm4.X86.FbLit
meta import VerifiedGarbage.Proof.Sm4.X86.FbFinalLit
meta import VerifiedGarbage.Proof.Sm4.X86.CtrLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM4 on x86 (32-bit), without secret residue

Key expansion and SM4's ECB, CBC, CFB128, OFB and CTR functions, and the
final pieces of CFB128, OFB and CTR, run with their working space in a frame
on the stack, wiped before they return (`withStackScratchWiped`). Key
expansion calls nothing in its frame: as emitted
(`Impl.Sm4.X86.Fn.expandKey`) it then clears the registers alone
(`X86.Scrub.verifiedScrubbedWiped`). As emitted (`Impl.Sm4.X86.Fn`), each of
the others then zeroes, of the stack its contract reserves below `esp`,
only the 10 to 22 doublewords that the residue analysis (`X86.rtaint`) finds
it may leave different in two runs (the header of its frame and the frames
of the calls below it), clears the registers a callee may change, and
returns without secret residue (`X86.Scrub.verifiedScrubbedSel`, the kernel
evaluating the analysis: `taint_decide_ct`), given that its postcondition
reads the memory on return only within the buffers (`Proof/Sm4/Scratch.lean`,
`CbcScratch.lean`, `FbScratch.lean`, `CtrFinal.lean` and
`Proof/Modes/CfbFinalScratch.lean`, for any pointer width). `vg_sm4_ctr_final` calls `vg_sm4_ctr`'s code as an internal
function of its own, `vg_sm4_ctr_core` (`Impl.Sm4.X86.ctrFramed`), and
SM4-GCM `vg_sm4_expand_key`'s as `vg_sm4_expand_key_core`
(`Impl.Sm4Gcm.X86.keyFn`).
-/

@[expose] public section

namespace VG.Proof.Sm4.X86.Scrub

open VG.X86 VG.X86.Scrub
open Impl.StackScratch.X86 (withStackScratchWiped)

/-! ## Postconditions -/

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
  verifiedScrubbedWiped (sig := Spec.Sm4.expandKeySig) (nm := "scratch") (e := .u64) (n := 179)
    (post := Proof.Sm4.expandKeyPost X86.abi.ptrBits) (bytes := 1448) (words := 358)
    Proof.Sm4.X86.expandKey_verified (by decide) (by decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.expandKeyPost_local _) (Proof.Sm4.expandKeyPostOut_local _) Proof.Sm4.X86.expandKeyFrameSat_pre rfl

/-- `Spec.Sm4.ecbEncryptApi`'s function as emitted (`Impl.Sm4.X86.Fn.ecbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.ecbEncrypt (Spec.Sm4.ecbContract X86.abi (Proof.Sm4.specDirX86 .encrypt) 1512) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ecbEncryptApi) (W := 1512)
    { code := withStackScratchWiped 1492 3 368 (Impl.Sm4.X86.ecb .encrypt)
      verified := Proof.Sm4.X86.ecb_framed .encrypt }
    Impl.Sm4.X86.Fn.ecbWords (ecbOut _ _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.ecbDecryptApi`'s function as emitted (`Impl.Sm4.X86.Fn.ecbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.ecbDecrypt (Spec.Sm4.ecbContract X86.abi (Proof.Sm4.specDirX86 .decrypt) 1512) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ecbDecryptApi) (W := 1512)
    { code := withStackScratchWiped 1492 3 368 (Impl.Sm4.X86.ecb .decrypt)
      verified := Proof.Sm4.X86.ecb_framed .decrypt }
    Impl.Sm4.X86.Fn.ecbWords (ecbOut _ _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.cbcEncryptChainedApi`'s function as emitted (`Impl.Sm4.X86.Fn.cbcEncryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.cbcEncryptChained (Spec.Sm4.cbcEncryptChainedContract X86.abi 1516) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cbcEncryptChainedApi) (W := 1516)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cbcEncryptChained
      verified := Proof.Sm4.X86.Cbc.cbcEncryptChained_framed }
    Impl.Sm4.X86.Fn.modeWords (cbcEncryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.cbcDecryptChainedApi`'s function as emitted (`Impl.Sm4.X86.Fn.cbcDecryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.cbcDecryptChained (Spec.Sm4.cbcDecryptChainedContract X86.abi 1516) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cbcDecryptChainedApi) (W := 1516)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cbcDecryptChained
      verified := Proof.Sm4.X86.Cbc.cbcDecryptChained_framed }
    Impl.Sm4.X86.Fn.modeWords (cbcDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.cfbEncryptApi`'s function as emitted (`Impl.Sm4.X86.Fn.cfbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.cfbEncrypt (Spec.Sm4.cfbEncryptContract X86.abi 1516) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cfbEncryptApi) (W := 1516)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbEncrypt
      verified := Proof.Sm4.X86.Fb.cfbEncrypt_framed }
    Impl.Sm4.X86.Fn.modeWords (cfbEncryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.cfbDecryptApi`'s function as emitted (`Impl.Sm4.X86.Fn.cfbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.cfbDecrypt (Spec.Sm4.cfbDecryptContract X86.abi 1516) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cfbDecryptApi) (W := 1516)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbDecrypt
      verified := Proof.Sm4.X86.Fb.cfbDecrypt_framed }
    Impl.Sm4.X86.Fn.modeWords (cfbDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.cfbEncryptFinalApi`'s function as emitted (`Impl.Sm4.X86.Fn.cfbEncryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.cfbEncryptFinal (Spec.Sm4.cfbEncryptFinalContract X86.abi 1516) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cfbEncryptFinalApi) (W := 1516)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbEncryptFinal
      verified := Proof.Sm4.X86.FbFinal.cfbEncryptFinal_framed }
    Impl.Sm4.X86.Fn.modeWords (cfbEncryptFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.cfbDecryptFinalApi`'s function as emitted (`Impl.Sm4.X86.Fn.cfbDecryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.cfbDecryptFinal (Spec.Sm4.cfbDecryptFinalContract X86.abi 1516) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cfbDecryptFinalApi) (W := 1516)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbDecryptFinal
      verified := Proof.Sm4.X86.FbFinal.cfbDecryptFinal_framed }
    Impl.Sm4.X86.Fn.modeWords (cfbDecryptFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.ofbApi`'s function as emitted (`Impl.Sm4.X86.Fn.ofb`) meets its contract
in constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.ofb (Spec.Sm4.ofbContract X86.abi 1516) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ofbApi) (W := 1516)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ofb
      verified := Proof.Sm4.X86.Fb.ofb_framed }
    Impl.Sm4.X86.Fn.modeWords (ofbOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.ofbFinalApi`'s function as emitted (`Impl.Sm4.X86.Fn.ofbFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.ofbFinal (Spec.Sm4.ofbFinalContract X86.abi 1516) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ofbFinalApi) (W := 1516)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ofbFinal
      verified := Proof.Sm4.X86.FbFinal.ofbFinal_framed }
    Impl.Sm4.X86.Fn.modeWords (ofbFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.ctrApi`'s function as emitted (`Impl.Sm4.X86.Fn.ctr`) meets its contract
in constant time and returns without secret residue. -/
theorem ctr_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.ctr (Spec.Sm4.ctrContract X86.abi 1516) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ctrApi) (W := 1516)
    { code := withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ctr
      verified := Proof.Sm4.X86.Ctr.ctr_framed }
    Impl.Sm4.X86.Fn.modeWords (ctrOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.ctrFinalApi`'s function as emitted (`Impl.Sm4.X86.Fn.ctrFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem ctrFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.Fn.ctrFinal (Spec.Sm4.ctrFinalContract X86.abi 1592) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ctrFinalApi) (W := 1592)
    { code := withStackScratchWiped 56 4 8 Impl.Sm4.X86.ctrFinal
      verified := Proof.Sm4.X86.CtrFinal.ctrFinal_framed
      spSafe := Proof.Sm4.X86.CtrFinal.ctrFinal_framed_spSafe }
    Impl.Sm4.X86.Fn.ctrFinalWords (ctrFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.Sm4.X86.Scrub
