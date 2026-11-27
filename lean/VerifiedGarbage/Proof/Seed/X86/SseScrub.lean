module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Impl.Seed.X86.SseFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Seed.Cbc
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.CfbFinal
public import VerifiedGarbage.Spec.Seed.Ofb
public import VerifiedGarbage.Spec.Seed.OfbFinal
public import VerifiedGarbage.Proof.Seed.X86.SseModes
public import VerifiedGarbage.Proof.Seed.X86.SseFbFinal
import VerifiedGarbage.Proof.Seed.X86.SseLit
import VerifiedGarbage.Proof.Seed.CbcScratch
import VerifiedGarbage.Proof.Seed.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Impl.Seed.X86.SseFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Seed.Cbc
meta import VerifiedGarbage.Spec.Seed.Cfb
meta import VerifiedGarbage.Spec.Seed.CfbFinal
meta import VerifiedGarbage.Spec.Seed.Ofb
meta import VerifiedGarbage.Spec.Seed.OfbFinal
meta import VerifiedGarbage.Proof.Seed.X86.SseModes
meta import VerifiedGarbage.Proof.Seed.X86.SseFbFinal
meta import VerifiedGarbage.Proof.Seed.X86.SseLit
meta import VerifiedGarbage.Proof.Seed.CbcScratch
meta import VerifiedGarbage.Proof.Seed.FbScratch
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.TaintCTAll
public meta import VerifiedGarbage.Proof.Framework.TaintCTAll

/-!
# SEED's chained modes on x86 (32-bit) in XMM registers, without secret residue

The functions as emitted (`Impl.Seed.X86.Sse.Fn`): each runs with its
working space in a frame on the stack, which it wipes, then zeroes, of the
1868 bytes of stack its contract reserves below `esp`, the nine doublewords
that the residue analysis (`X86.rtaint`) finds it may leave different in two
runs (where the core calls its functions, the header of that frame and its
last doubleword), clears the registers a callee may change, and returns without secret residue (`X86.Scrub.verifiedScrubbedSel`, the
kernel evaluating the analysis of the code with its cleanup:
`taint_decide_ct`). Their postconditions read the memory on return only
within their buffers (`Proof/Seed/CbcScratch.lean`, `FbScratch.lean` and
`Proof/Modes/CfbFinalScratch.lean`, for any pointer width).
-/

@[expose] public section

namespace VG.Proof.Seed.X86.Sse.Scrub

open VG.X86 VG.X86.Scrub

/-! ## Postconditions -/

theorem cbcEncryptOut (stack : Nat) :
    PostOut (Spec.Seed.cbcEncryptChainedContract X86.abi stack) (Spec.Seed.cbcChainedSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Seed.cbcEncChainedPostOut_local _)

theorem cfbEncryptOut (stack : Nat) : PostOut (Spec.Seed.cfbEncryptContract X86.abi stack) (Spec.Seed.cfbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Seed.cfbEncPostOut_local _)

theorem cfbEncryptFinalOut (stack : Nat) :
    PostOut (Spec.Seed.cfbEncryptFinalContract X86.abi stack) (Spec.Seed.cfbFinalSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptFinalOut (stack : Nat) :
    PostOut (Spec.Seed.cfbDecryptFinalContract X86.abi stack) (Spec.Seed.cfbFinalSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem ofbOut (stack : Nat) : PostOut (Spec.Seed.ofbContract X86.abi stack) (Spec.Seed.ofbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Seed.ofbPostOut_local _)

theorem ofbFinalOut (stack : Nat) :
    PostOut (Spec.Seed.ofbFinalContract X86.abi stack) (Spec.Seed.ofbFinalSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

theorem cbcDecryptOut (stack : Nat) :
    PostOut (Spec.Seed.cbcDecryptChainedContract X86.abi stack) (Spec.Seed.cbcChainedSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Seed.cbcDecChainedPostOut_local _)

theorem cfbDecryptOut (stack : Nat) : PostOut (Spec.Seed.cfbDecryptContract X86.abi stack) (Spec.Seed.cfbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Seed.cfbDecPostOut_local _)

/-! ## The functions as emitted -/

/-- The residue analyses of the functions' code, in one kernel evaluation
(`taint_decide_ct_all`), which analyses the code they share once. -/
theorem residue :
    rtaint.Ends (RTaint.init 1868 0) Impl.Seed.X86.Sse.Fn.cbcEncryptChained (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 1868 0) Impl.Seed.X86.Sse.Fn.ofb (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 1868 0) Impl.Seed.X86.Sse.Fn.ofbFinal (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 1868 0) Impl.Seed.X86.Sse.Fn.cfbEncrypt (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 1868 0) Impl.Seed.X86.Sse.Fn.cfbEncryptFinal (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 1868 0) Impl.Seed.X86.Sse.Fn.cfbDecryptFinal (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 1868 0) Impl.Seed.X86.Sse.Fn.cbcDecryptChained (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 1868 0) Impl.Seed.X86.Sse.Fn.cfbDecrypt (RTaint.done 0) := by
  taint_decide_ct_all

/-- `Spec.Seed.cbcEncryptChainedApi` as emitted (`Impl.Seed.X86.Sse.Fn.cbcEncryptChained`) meets its contract in constant
time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.Sse.Fn.cbcEncryptChained (Spec.Seed.cbcEncryptChainedContract X86.abi 1868) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cbcEncryptChainedApi) (W := 1868)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.cbcEncryptChained
      verified := Proof.Seed.X86.Sse.Modes.cbcEncryptChained_framed }
    Impl.Seed.X86.Sse.Fn.modeWords (cbcEncryptOut _) (by decide) residue.1

/-- `Spec.Seed.ofbApi` as emitted (`Impl.Seed.X86.Sse.Fn.ofb`) meets its contract in constant
time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.Sse.Fn.ofb (Spec.Seed.ofbContract X86.abi 1868) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.ofbApi) (W := 1868)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.ofb
      verified := Proof.Seed.X86.Sse.Modes.ofb_framed }
    Impl.Seed.X86.Sse.Fn.modeWords (ofbOut _) (by decide) residue.2.1

/-- `Spec.Seed.ofbFinalApi` as emitted (`Impl.Seed.X86.Sse.Fn.ofbFinal`) meets its contract in constant
time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.Sse.Fn.ofbFinal (Spec.Seed.ofbFinalContract X86.abi 1868) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.ofbFinalApi) (W := 1868)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.ofbFinal
      verified := Proof.Seed.X86.Sse.FbFinal.ofbFinal_framed }
    Impl.Seed.X86.Sse.Fn.modeWords (ofbFinalOut _) (by decide) residue.2.2.1

/-- `Spec.Seed.cfbEncryptApi` as emitted (`Impl.Seed.X86.Sse.Fn.cfbEncrypt`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.Sse.Fn.cfbEncrypt (Spec.Seed.cfbEncryptContract X86.abi 1868) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cfbEncryptApi) (W := 1868)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.cfbEncrypt
      verified := Proof.Seed.X86.Sse.Modes.cfbEncrypt_framed }
    Impl.Seed.X86.Sse.Fn.modeWords (cfbEncryptOut _) (by decide) residue.2.2.2.1

/-- `Spec.Seed.cfbEncryptFinalApi` as emitted (`Impl.Seed.X86.Sse.Fn.cfbEncryptFinal`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.Sse.Fn.cfbEncryptFinal (Spec.Seed.cfbEncryptFinalContract X86.abi 1868) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cfbEncryptFinalApi) (W := 1868)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.cfbEncryptFinal
      verified := Proof.Seed.X86.Sse.FbFinal.cfbEncryptFinal_framed }
    Impl.Seed.X86.Sse.Fn.modeWords (cfbEncryptFinalOut _) (by decide) residue.2.2.2.2.1

/-- `Spec.Seed.cfbDecryptFinalApi` as emitted (`Impl.Seed.X86.Sse.Fn.cfbDecryptFinal`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.Sse.Fn.cfbDecryptFinal (Spec.Seed.cfbDecryptFinalContract X86.abi 1868) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cfbDecryptFinalApi) (W := 1868)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.cfbDecryptFinal
      verified := Proof.Seed.X86.Sse.FbFinal.cfbDecryptFinal_framed }
    Impl.Seed.X86.Sse.Fn.modeWords (cfbDecryptFinalOut _) (by decide) residue.2.2.2.2.2.1

/-- `Spec.Seed.cbcDecryptChainedApi` as emitted (`Impl.Seed.X86.Sse.Fn.cbcDecryptChained`) meets its
contract in constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.Sse.Fn.cbcDecryptChained
      (Spec.Seed.cbcDecryptChainedContract X86.abi 1868) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cbcDecryptChainedApi) (W := 1868)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.cbcDecryptChained
      verified := Proof.Seed.X86.Sse.Modes.cbcDecryptChained_framed }
    Impl.Seed.X86.Sse.Fn.modeWords (cbcDecryptOut _) (by decide) residue.2.2.2.2.2.2.1

/-- `Spec.Seed.cfbDecryptApi` as emitted (`Impl.Seed.X86.Sse.Fn.cfbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.Sse.Fn.cfbDecrypt (Spec.Seed.cfbDecryptContract X86.abi 1868) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cfbDecryptApi) (W := 1868)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.cfbDecrypt
      verified := Proof.Seed.X86.Sse.Modes.cfbDecrypt_framed }
    Impl.Seed.X86.Sse.Fn.modeWords (cfbDecryptOut _) (by decide) residue.2.2.2.2.2.2.2

end VG.Proof.Seed.X86.Sse.Scrub
