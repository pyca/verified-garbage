module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Impl.Camellia.X86.AesNiWideFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Camellia.X86.Scrub
public import VerifiedGarbage.Proof.Camellia.X86.AesNiWideModes
import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Impl.Camellia.X86.AesNiWideFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Camellia.X86.Scrub
meta import VerifiedGarbage.Proof.Camellia.X86.AesNiWideModes
meta import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Camellia's wide modes by the AES S-box on x86 (32-bit), without secret residue

The functions as emitted (`Impl.Camellia.X86.AesNiWide.Fn`): each runs with
its working space in a frame on the stack, which it wipes, then zeroes, of
the 892 bytes of stack its contract reserves below `esp`, the seven
doublewords that the residue analysis (`X86.rtaint`) finds it may leave
different in two runs, the header of that frame, clears the registers a
callee may change, and returns without secret residue
(`X86.Scrub.verifiedScrubbedSel`, the kernel evaluating the analysis of the
code with its cleanup: `taint_decide_ct`). Their postconditions read the
memory on return only within their buffers
(`Proof/Camellia/X86/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.AesNiWide.Scrub

open VG.X86 VG.X86.Scrub
open VG.Proof.Camellia.X86.Scrub (cbcDecryptOut cfbDecryptOut ctrOut)

/-- `Spec.Camellia.cbcDecryptChainedApi` as emitted
(`Impl.Camellia.X86.AesNiWide.Fn.cbcDecryptChained`) meets its contract in
constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.AesNiWide.Fn.cbcDecryptChained
      (Spec.Camellia.cbcDecryptChainedContract X86.abi 892) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cbcDecryptChainedApi) (W := 892)
    { code := Impl.StackScratch.X86.withStackScratchWiped 888 5 214 Impl.Camellia.X86.AesNiWide.cbcDecryptChained
      verified := Proof.Camellia.X86.AesNiWide.Modes.cbcDecryptChained_framed }
    Impl.Camellia.X86.AesNiWide.Fn.modeWords (cbcDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.cfbDecryptApi` as emitted (`Impl.Camellia.X86.AesNiWide.Fn.cfbDecrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.AesNiWide.Fn.cfbDecrypt
      (Spec.Camellia.cfbDecryptContract X86.abi 892) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbDecryptApi) (W := 892)
    { code := Impl.StackScratch.X86.withStackScratchWiped 888 5 214 Impl.Camellia.X86.AesNiWide.cfbDecrypt
      verified := Proof.Camellia.X86.AesNiWide.Modes.cfbDecrypt_framed }
    Impl.Camellia.X86.AesNiWide.Fn.modeWords (cfbDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.ctrApi` as emitted (`Impl.Camellia.X86.AesNiWide.Fn.ctr`) meets its
contract in constant time and returns without secret residue. -/
theorem ctr_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.AesNiWide.Fn.ctr (Spec.Camellia.ctrContract X86.abi 892) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ctrApi) (W := 892)
    { code := Impl.StackScratch.X86.withStackScratchWiped 888 5 214 Impl.Camellia.X86.AesNiWide.ctr
      verified := Proof.Camellia.X86.AesNiWide.Modes.ctr_framed }
    Impl.Camellia.X86.AesNiWide.Fn.modeWords (ctrOut _) (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.Camellia.X86.AesNiWide.Scrub
