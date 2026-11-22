module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Impl.Sm4.X86.AesNiFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4.X86.Scrub
public import VerifiedGarbage.Proof.Sm4.X86.AesNiFb
public import VerifiedGarbage.Proof.Sm4.X86.AesNiFbFinal
import VerifiedGarbage.Proof.Sm4.X86.AesNiLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Impl.Sm4.X86.AesNiFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sm4.X86.Scrub
meta import VerifiedGarbage.Proof.Sm4.X86.AesNiFb
meta import VerifiedGarbage.Proof.Sm4.X86.AesNiFbFinal
meta import VerifiedGarbage.Proof.Sm4.X86.AesNiLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM4's chained modes by the AES S-box on x86 (32-bit), without secret residue

The functions as emitted (`Impl.Sm4.X86.AesNi.Fn`): each runs with its
working space in a frame on the stack, which it wipes, then zeroes, of the
692 bytes of stack its contract reserves below `esp`, the six doublewords
that the residue analysis (`X86.rtaint`) finds it may leave different in two
runs, the header of that frame, clears the registers a callee may change,
and returns without secret residue (`X86.Scrub.verifiedScrubbedSel`, the
kernel evaluating the analysis of the code with its cleanup:
`taint_decide_ct`). Their postconditions read the memory on return only
within their buffers (`Proof/Sm4/X86/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm4.X86.AesNi.Scrub

open VG.X86 VG.X86.Scrub
open VG.Proof.Sm4.X86.Scrub (cbcEncryptOut cfbEncryptOut ofbOut cfbEncryptFinalOut cfbDecryptFinalOut ofbFinalOut)

/-- `Spec.Sm4.cbcEncryptChainedApi` as emitted (`Impl.Sm4.X86.AesNi.Fn.cbcEncryptChained`) meets its contract in constant
time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.AesNi.Fn.cbcEncryptChained (Spec.Sm4.cbcEncryptChainedContract X86.abi 692) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cbcEncryptChainedApi) (W := 692)
    { code := Impl.StackScratch.X86.withStackScratchWiped 688 4 166 Impl.Sm4.X86.AesNi.cbcEncryptChained
      verified := Proof.Sm4.X86.AesNi.Fb.cbcEncryptChained_framed }
    Impl.Sm4.X86.AesNi.Fn.modeWords (cbcEncryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.ofbApi` as emitted (`Impl.Sm4.X86.AesNi.Fn.ofb`) meets its contract in constant
time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.AesNi.Fn.ofb (Spec.Sm4.ofbContract X86.abi 692) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ofbApi) (W := 692)
    { code := Impl.StackScratch.X86.withStackScratchWiped 688 4 166 Impl.Sm4.X86.AesNi.ofb
      verified := Proof.Sm4.X86.AesNi.Fb.ofb_framed }
    Impl.Sm4.X86.AesNi.Fn.modeWords (ofbOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.ofbFinalApi` as emitted (`Impl.Sm4.X86.AesNi.Fn.ofbFinal`) meets its contract in constant
time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.AesNi.Fn.ofbFinal (Spec.Sm4.ofbFinalContract X86.abi 692) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ofbFinalApi) (W := 692)
    { code := Impl.StackScratch.X86.withStackScratchWiped 688 4 166 Impl.Sm4.X86.AesNi.ofbFinal
      verified := Proof.Sm4.X86.AesNi.FbFinal.ofbFinal_framed }
    Impl.Sm4.X86.AesNi.Fn.modeWords (ofbFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.cfbEncryptApi` as emitted (`Impl.Sm4.X86.AesNi.Fn.cfbEncrypt`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.AesNi.Fn.cfbEncrypt (Spec.Sm4.cfbEncryptContract X86.abi 692) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cfbEncryptApi) (W := 692)
    { code := Impl.StackScratch.X86.withStackScratchWiped 688 4 166 Impl.Sm4.X86.AesNi.cfbEncrypt
      verified := Proof.Sm4.X86.AesNi.Fb.cfbEncrypt_framed }
    Impl.Sm4.X86.AesNi.Fn.modeWords (cfbEncryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.cfbEncryptFinalApi` as emitted (`Impl.Sm4.X86.AesNi.Fn.cfbEncryptFinal`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.AesNi.Fn.cfbEncryptFinal (Spec.Sm4.cfbEncryptFinalContract X86.abi 692) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cfbEncryptFinalApi) (W := 692)
    { code := Impl.StackScratch.X86.withStackScratchWiped 688 4 166 Impl.Sm4.X86.AesNi.cfbEncryptFinal
      verified := Proof.Sm4.X86.AesNi.FbFinal.cfbEncryptFinal_framed }
    Impl.Sm4.X86.AesNi.Fn.modeWords (cfbEncryptFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.cfbDecryptFinalApi` as emitted (`Impl.Sm4.X86.AesNi.Fn.cfbDecryptFinal`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.AesNi.Fn.cfbDecryptFinal (Spec.Sm4.cfbDecryptFinalContract X86.abi 692) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cfbDecryptFinalApi) (W := 692)
    { code := Impl.StackScratch.X86.withStackScratchWiped 688 4 166 Impl.Sm4.X86.AesNi.cfbDecryptFinal
      verified := Proof.Sm4.X86.AesNi.FbFinal.cfbDecryptFinal_framed }
    Impl.Sm4.X86.AesNi.Fn.modeWords (cfbDecryptFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.Sm4.X86.AesNi.Scrub
