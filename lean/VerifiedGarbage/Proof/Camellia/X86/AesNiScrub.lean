module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Impl.Camellia.X86.AesNiFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Camellia.X86.Scrub
public import VerifiedGarbage.Proof.Camellia.X86.AesNiFb
public import VerifiedGarbage.Proof.Camellia.X86.AesNiFbFinal
import VerifiedGarbage.Proof.Camellia.X86.AesNiLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Impl.Camellia.X86.AesNiFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Camellia.X86.Scrub
meta import VerifiedGarbage.Proof.Camellia.X86.AesNiFb
meta import VerifiedGarbage.Proof.Camellia.X86.AesNiFbFinal
meta import VerifiedGarbage.Proof.Camellia.X86.AesNiLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Camellia's chained modes by the AES S-box on x86 (32-bit), without secret residue

The functions as emitted (`Impl.Camellia.X86.AesNi.Fn`): each runs with its
working space in a frame on the stack, which it wipes, then zeroes, of the
576 bytes of stack its contract reserves below `esp`, the seven doublewords
that the residue analysis (`X86.rtaint`) finds it may leave different in two
runs, the header of that frame, clears the registers a callee may change,
and returns without secret residue (`X86.Scrub.verifiedScrubbedSel`, the
kernel evaluating the analysis of the code with its cleanup:
`taint_decide_ct`). Their postconditions read the memory on return only
within their buffers (`Proof/Camellia/X86/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.AesNi.Scrub

open VG.X86 VG.X86.Scrub VG.Spec.Camellia
open VG.Proof.Camellia.X86.Scrub (cbcEncryptOut cfbEncryptOut ofbOut cfbEncryptFinalOut cfbDecryptFinalOut ofbFinalOut)

/-- `Spec.Camellia.cbcEncryptChainedApi` as emitted (`Impl.Camellia.X86.AesNi.Fn.cbcEncryptChained`) meets its
contract in constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.AesNi.Fn.cbcEncryptChained
      (Spec.Camellia.cbcEncryptChainedContract X86.abi 576) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cbcEncryptChainedApi) (W := 576)
    { code := Impl.StackScratch.X86.withStackScratchWiped 572 5 136 Impl.Camellia.X86.AesNi.cbcEncryptChained
      verified := Proof.Camellia.X86.AesNi.Fb.cbcEncryptChained_framed }
    Impl.Camellia.X86.AesNi.Fn.modeWords (cbcEncryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.ofbApi` as emitted (`Impl.Camellia.X86.AesNi.Fn.ofb`) meets its contract in constant time
and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.AesNi.Fn.ofb (Spec.Camellia.ofbContract X86.abi 576) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ofbApi) (W := 576)
    { code := Impl.StackScratch.X86.withStackScratchWiped 572 5 136 Impl.Camellia.X86.AesNi.ofb
      verified := Proof.Camellia.X86.AesNi.Fb.ofb_framed }
    Impl.Camellia.X86.AesNi.Fn.modeWords (ofbOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.ofbFinalApi` as emitted (`Impl.Camellia.X86.AesNi.Fn.ofbFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.AesNi.Fn.ofbFinal (Spec.Camellia.ofbFinalContract X86.abi 576) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ofbFinalApi) (W := 576)
    { code := Impl.StackScratch.X86.withStackScratchWiped 572 5 136 Impl.Camellia.X86.AesNi.ofbFinal
      verified := Proof.Camellia.X86.AesNi.FbFinal.ofbFinal_framed }
    Impl.Camellia.X86.AesNi.Fn.modeWords (ofbFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.cfbEncryptApi` as emitted (`Impl.Camellia.X86.AesNi.Fn.cfbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.AesNi.Fn.cfbEncrypt
      (Spec.Camellia.cfbEncryptContract X86.abi 576) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbEncryptApi) (W := 576)
    { code := Impl.StackScratch.X86.withStackScratchWiped 572 5 136 Impl.Camellia.X86.AesNi.cfbEncrypt
      verified := Proof.Camellia.X86.AesNi.Fb.cfbEncrypt_framed }
    Impl.Camellia.X86.AesNi.Fn.modeWords (cfbEncryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.cfbEncryptFinalApi` as emitted (`Impl.Camellia.X86.AesNi.Fn.cfbEncryptFinal`) meets its
contract in constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.AesNi.Fn.cfbEncryptFinal
      (Spec.Camellia.cfbEncryptFinalContract X86.abi 576) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbEncryptFinalApi) (W := 576)
    { code := Impl.StackScratch.X86.withStackScratchWiped 572 5 136 Impl.Camellia.X86.AesNi.cfbEncryptFinal
      verified := Proof.Camellia.X86.AesNi.FbFinal.cfbEncryptFinal_framed }
    Impl.Camellia.X86.AesNi.Fn.modeWords (cfbEncryptFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.cfbDecryptFinalApi` as emitted (`Impl.Camellia.X86.AesNi.Fn.cfbDecryptFinal`) meets its
contract in constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.AesNi.Fn.cfbDecryptFinal
      (Spec.Camellia.cfbDecryptFinalContract X86.abi 576) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbDecryptFinalApi) (W := 576)
    { code := Impl.StackScratch.X86.withStackScratchWiped 572 5 136 Impl.Camellia.X86.AesNi.cfbDecryptFinal
      verified := Proof.Camellia.X86.AesNi.FbFinal.cfbDecryptFinal_framed }
    Impl.Camellia.X86.AesNi.Fn.modeWords (cfbDecryptFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.Camellia.X86.AesNi.Scrub
