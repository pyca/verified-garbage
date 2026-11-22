module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Impl.Sm4.X86.AesNiWideFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4.X86.Scrub
public import VerifiedGarbage.Proof.Sm4.X86.AesNiWideModes
import VerifiedGarbage.Proof.Sm4.X86.AesNiWideLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Impl.Sm4.X86.AesNiWideFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sm4.X86.Scrub
meta import VerifiedGarbage.Proof.Sm4.X86.AesNiWideModes
meta import VerifiedGarbage.Proof.Sm4.X86.AesNiWideLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM4's wide modes by the AES S-box on x86 (32-bit), without secret residue

The functions as emitted (`Impl.Sm4.X86.AesNiWide.Fn`): each runs with its
working space in a frame on the stack, which it wipes, then zeroes, of the
756 bytes of stack its contract reserves below `esp`, the six doublewords
that the residue analysis (`X86.rtaint`) finds it may leave different in two
runs, the header of that frame, clears the registers a callee may change,
and returns without secret residue (`X86.Scrub.verifiedScrubbedSel`, the
kernel evaluating the analysis of the code with its cleanup:
`taint_decide_ct`). Their postconditions read the memory on return only
within their buffers (`Proof/Sm4/X86/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm4.X86.AesNiWide.Scrub

open VG.X86 VG.X86.Scrub
open VG.Proof.Sm4.X86.Scrub (cbcDecryptOut cfbDecryptOut ctrOut)

/-- `Spec.Sm4.cbcDecryptChainedApi` as emitted (`Impl.Sm4.X86.AesNiWide.Fn.cbcDecryptChained`) meets its contract in constant
time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.AesNiWide.Fn.cbcDecryptChained (Spec.Sm4.cbcDecryptChainedContract X86.abi 756) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cbcDecryptChainedApi) (W := 756)
    { code := Impl.StackScratch.X86.withStackScratchWiped 752 4 182 Impl.Sm4.X86.AesNiWide.cbcDecryptChained
      verified := Proof.Sm4.X86.AesNiWide.Modes.cbcDecryptChained_framed }
    Impl.Sm4.X86.AesNiWide.Fn.modeWords (cbcDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.cfbDecryptApi` as emitted (`Impl.Sm4.X86.AesNiWide.Fn.cfbDecrypt`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.AesNiWide.Fn.cfbDecrypt (Spec.Sm4.cfbDecryptContract X86.abi 756) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cfbDecryptApi) (W := 756)
    { code := Impl.StackScratch.X86.withStackScratchWiped 752 4 182 Impl.Sm4.X86.AesNiWide.cfbDecrypt
      verified := Proof.Sm4.X86.AesNiWide.Modes.cfbDecrypt_framed }
    Impl.Sm4.X86.AesNiWide.Fn.modeWords (cfbDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Sm4.ctrApi` as emitted (`Impl.Sm4.X86.AesNiWide.Fn.ctr`) meets its contract in constant
time and returns without secret residue. -/
theorem ctr_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.AesNiWide.Fn.ctr (Spec.Sm4.ctrContract X86.abi 756) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ctrApi) (W := 756)
    { code := Impl.StackScratch.X86.withStackScratchWiped 752 4 182 Impl.Sm4.X86.AesNiWide.ctr
      verified := Proof.Sm4.X86.AesNiWide.Modes.ctr_framed }
    Impl.Sm4.X86.AesNiWide.Fn.modeWords (ctrOut _) (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.Sm4.X86.AesNiWide.Scrub
