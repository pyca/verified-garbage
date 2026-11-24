module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Impl.Seed.X86.AesNiFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Seed.Cbc
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.CfbFinal
public import VerifiedGarbage.Spec.Seed.Ofb
public import VerifiedGarbage.Spec.Seed.OfbFinal
public import VerifiedGarbage.Proof.Seed.X86.AesNiFb
public import VerifiedGarbage.Proof.Seed.X86.AesNiFbFinal
import VerifiedGarbage.Proof.Seed.X86.AesNiLit
import VerifiedGarbage.Proof.Seed.CbcScratch
import VerifiedGarbage.Proof.Seed.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Impl.Seed.X86.AesNiFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Seed.Cbc
meta import VerifiedGarbage.Spec.Seed.Cfb
meta import VerifiedGarbage.Spec.Seed.CfbFinal
meta import VerifiedGarbage.Spec.Seed.Ofb
meta import VerifiedGarbage.Spec.Seed.OfbFinal
meta import VerifiedGarbage.Proof.Seed.X86.AesNiFb
meta import VerifiedGarbage.Proof.Seed.X86.AesNiFbFinal
meta import VerifiedGarbage.Proof.Seed.X86.AesNiLit
meta import VerifiedGarbage.Proof.Seed.CbcScratch
meta import VerifiedGarbage.Proof.Seed.FbScratch
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SEED's chained modes by the AES S-box on x86 (32-bit), without secret residue

The functions as emitted (`Impl.Seed.X86.AesNi.Fn`): each runs with its
working space in a frame on the stack, which it wipes, then zeroes, of the
676 bytes of stack its contract reserves below `esp`, the six doublewords
that the residue analysis (`X86.rtaint`) finds it may leave different in two
runs, the header of that frame, clears the registers a callee may change,
and returns without secret residue (`X86.Scrub.verifiedScrubbedSel`, the
kernel evaluating the analysis of the code with its cleanup:
`taint_decide_ct`). Their postconditions read the memory on return only
within their buffers (`Proof/Seed/CbcScratch.lean`, `FbScratch.lean` and
`Proof/Modes/CfbFinalScratch.lean`, for any pointer width).
-/

@[expose] public section

namespace VG.Proof.Seed.X86.AesNi.Scrub

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

/-! ## The functions as emitted -/

/-- `Spec.Seed.cbcEncryptChainedApi` as emitted (`Impl.Seed.X86.AesNi.Fn.cbcEncryptChained`) meets its contract in constant
time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.AesNi.Fn.cbcEncryptChained (Spec.Seed.cbcEncryptChainedContract X86.abi 676) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cbcEncryptChainedApi) (W := 676)
    { code := Impl.StackScratch.X86.withStackScratchWiped 672 4 162 Impl.Seed.X86.AesNi.cbcEncryptChained
      verified := Proof.Seed.X86.AesNi.Fb.cbcEncryptChained_framed }
    Impl.Seed.X86.AesNi.Fn.modeWords (cbcEncryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Seed.ofbApi` as emitted (`Impl.Seed.X86.AesNi.Fn.ofb`) meets its contract in constant
time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.AesNi.Fn.ofb (Spec.Seed.ofbContract X86.abi 676) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.ofbApi) (W := 676)
    { code := Impl.StackScratch.X86.withStackScratchWiped 672 4 162 Impl.Seed.X86.AesNi.ofb
      verified := Proof.Seed.X86.AesNi.Fb.ofb_framed }
    Impl.Seed.X86.AesNi.Fn.modeWords (ofbOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Seed.ofbFinalApi` as emitted (`Impl.Seed.X86.AesNi.Fn.ofbFinal`) meets its contract in constant
time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.AesNi.Fn.ofbFinal (Spec.Seed.ofbFinalContract X86.abi 676) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.ofbFinalApi) (W := 676)
    { code := Impl.StackScratch.X86.withStackScratchWiped 672 4 162 Impl.Seed.X86.AesNi.ofbFinal
      verified := Proof.Seed.X86.AesNi.FbFinal.ofbFinal_framed }
    Impl.Seed.X86.AesNi.Fn.modeWords (ofbFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Seed.cfbEncryptApi` as emitted (`Impl.Seed.X86.AesNi.Fn.cfbEncrypt`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.AesNi.Fn.cfbEncrypt (Spec.Seed.cfbEncryptContract X86.abi 676) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cfbEncryptApi) (W := 676)
    { code := Impl.StackScratch.X86.withStackScratchWiped 672 4 162 Impl.Seed.X86.AesNi.cfbEncrypt
      verified := Proof.Seed.X86.AesNi.Fb.cfbEncrypt_framed }
    Impl.Seed.X86.AesNi.Fn.modeWords (cfbEncryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Seed.cfbEncryptFinalApi` as emitted (`Impl.Seed.X86.AesNi.Fn.cfbEncryptFinal`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.AesNi.Fn.cfbEncryptFinal (Spec.Seed.cfbEncryptFinalContract X86.abi 676) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cfbEncryptFinalApi) (W := 676)
    { code := Impl.StackScratch.X86.withStackScratchWiped 672 4 162 Impl.Seed.X86.AesNi.cfbEncryptFinal
      verified := Proof.Seed.X86.AesNi.FbFinal.cfbEncryptFinal_framed }
    Impl.Seed.X86.AesNi.Fn.modeWords (cfbEncryptFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Seed.cfbDecryptFinalApi` as emitted (`Impl.Seed.X86.AesNi.Fn.cfbDecryptFinal`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.AesNi.Fn.cfbDecryptFinal (Spec.Seed.cfbDecryptFinalContract X86.abi 676) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cfbDecryptFinalApi) (W := 676)
    { code := Impl.StackScratch.X86.withStackScratchWiped 672 4 162 Impl.Seed.X86.AesNi.cfbDecryptFinal
      verified := Proof.Seed.X86.AesNi.FbFinal.cfbDecryptFinal_framed }
    Impl.Seed.X86.AesNi.Fn.modeWords (cfbDecryptFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.Seed.X86.AesNi.Scrub
