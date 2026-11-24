module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Impl.Camellia.X86.SseFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Camellia.X86.Scrub
public import VerifiedGarbage.Proof.Camellia.X86.SseModes
public import VerifiedGarbage.Proof.Camellia.X86.SseFbFinal
import VerifiedGarbage.Proof.Camellia.X86.SseLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Impl.Camellia.X86.SseFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Camellia.X86.Scrub
meta import VerifiedGarbage.Proof.Camellia.X86.SseModes
meta import VerifiedGarbage.Proof.Camellia.X86.SseFbFinal
meta import VerifiedGarbage.Proof.Camellia.X86.SseLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Camellia's modes on x86 (32-bit) in XMM registers, without secret residue

The functions as emitted (`Impl.Camellia.X86.Sse.Fn`): each runs with its
working space in a frame on the stack, which it wipes, then zeroes, of the
1580 bytes of stack its contract reserves below `esp`, the nine doublewords
that the residue analysis (`X86.rtaint`) finds it may leave different in two
runs (where the core calls the block function, the header of that frame and
its last doubleword), clears the registers a callee may change, and returns
without secret residue (`X86.Scrub.verifiedScrubbedSel`, the kernel
evaluating the analysis of the code with its cleanup: `taint_decide_ct`).
Their postconditions read the memory on return only within their buffers
(`Proof/Camellia/X86/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.Sse.Scrub

open VG.X86 VG.X86.Scrub
open VG.Proof.Camellia.X86.Scrub (cbcDecryptOut cfbDecryptOut ctrOut cbcEncryptOut cfbEncryptOut ofbOut
  cfbEncryptFinalOut cfbDecryptFinalOut ofbFinalOut)

/-- `Spec.Camellia.cbcDecryptChainedApi` as emitted
(`Impl.Camellia.X86.Sse.Fn.cbcDecryptChained`) meets its contract in
constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Sse.Fn.cbcDecryptChained
      (Spec.Camellia.cbcDecryptChainedContract X86.abi 1580) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cbcDecryptChainedApi) (W := 1580)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.cbcDecryptChained
      verified := Proof.Camellia.X86.Sse.Modes.cbcDecryptChained_framed }
    Impl.Camellia.X86.Sse.Fn.modeWords (cbcDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.cfbDecryptApi` as emitted (`Impl.Camellia.X86.Sse.Fn.cfbDecrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Sse.Fn.cfbDecrypt
      (Spec.Camellia.cfbDecryptContract X86.abi 1580) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbDecryptApi) (W := 1580)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.cfbDecrypt
      verified := Proof.Camellia.X86.Sse.Modes.cfbDecrypt_framed }
    Impl.Camellia.X86.Sse.Fn.modeWords (cfbDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.ctrApi` as emitted (`Impl.Camellia.X86.Sse.Fn.ctr`) meets its
contract in constant time and returns without secret residue. -/
theorem ctr_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Sse.Fn.ctr (Spec.Camellia.ctrContract X86.abi 1580) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ctrApi) (W := 1580)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.ctr
      verified := Proof.Camellia.X86.Sse.Modes.ctr_framed }
    Impl.Camellia.X86.Sse.Fn.modeWords (ctrOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.cbcEncryptChainedApi` as emitted (`Impl.Camellia.X86.Sse.Fn.cbcEncryptChained`) meets its
contract in constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Sse.Fn.cbcEncryptChained
      (Spec.Camellia.cbcEncryptChainedContract X86.abi 1580) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cbcEncryptChainedApi) (W := 1580)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.cbcEncryptChained
      verified := Proof.Camellia.X86.Sse.Modes.cbcEncryptChained_framed }
    Impl.Camellia.X86.Sse.Fn.modeWords (cbcEncryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.ofbApi` as emitted (`Impl.Camellia.X86.Sse.Fn.ofb`) meets its contract in constant time
and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Sse.Fn.ofb (Spec.Camellia.ofbContract X86.abi 1580) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ofbApi) (W := 1580)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.ofb
      verified := Proof.Camellia.X86.Sse.Modes.ofb_framed }
    Impl.Camellia.X86.Sse.Fn.modeWords (ofbOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.ofbFinalApi` as emitted (`Impl.Camellia.X86.Sse.Fn.ofbFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Sse.Fn.ofbFinal (Spec.Camellia.ofbFinalContract X86.abi 1580) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ofbFinalApi) (W := 1580)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.ofbFinal
      verified := Proof.Camellia.X86.Sse.FbFinal.ofbFinal_framed }
    Impl.Camellia.X86.Sse.Fn.modeWords (ofbFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.cfbEncryptApi` as emitted (`Impl.Camellia.X86.Sse.Fn.cfbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Sse.Fn.cfbEncrypt
      (Spec.Camellia.cfbEncryptContract X86.abi 1580) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbEncryptApi) (W := 1580)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.cfbEncrypt
      verified := Proof.Camellia.X86.Sse.Modes.cfbEncrypt_framed }
    Impl.Camellia.X86.Sse.Fn.modeWords (cfbEncryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.cfbEncryptFinalApi` as emitted (`Impl.Camellia.X86.Sse.Fn.cfbEncryptFinal`) meets its
contract in constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Sse.Fn.cfbEncryptFinal
      (Spec.Camellia.cfbEncryptFinalContract X86.abi 1580) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbEncryptFinalApi) (W := 1580)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.cfbEncryptFinal
      verified := Proof.Camellia.X86.Sse.FbFinal.cfbEncryptFinal_framed }
    Impl.Camellia.X86.Sse.Fn.modeWords (cfbEncryptFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.cfbDecryptFinalApi` as emitted (`Impl.Camellia.X86.Sse.Fn.cfbDecryptFinal`) meets its
contract in constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Sse.Fn.cfbDecryptFinal
      (Spec.Camellia.cfbDecryptFinalContract X86.abi 1580) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbDecryptFinalApi) (W := 1580)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.cfbDecryptFinal
      verified := Proof.Camellia.X86.Sse.FbFinal.cfbDecryptFinal_framed }
    Impl.Camellia.X86.Sse.Fn.modeWords (cfbDecryptFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.Camellia.X86.Sse.Scrub
