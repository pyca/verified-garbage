module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Impl.Seed.X86.AesNiWideFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Seed.Cbc
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Proof.Seed.X86.AesNiWideModes
import VerifiedGarbage.Proof.Seed.X86.AesNiWideLit
import VerifiedGarbage.Proof.Seed.CbcScratch
import VerifiedGarbage.Proof.Seed.FbScratch
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Impl.Seed.X86.AesNiWideFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Seed.Cbc
meta import VerifiedGarbage.Spec.Seed.Cfb
meta import VerifiedGarbage.Proof.Seed.X86.AesNiWideModes
meta import VerifiedGarbage.Proof.Seed.X86.AesNiWideLit
meta import VerifiedGarbage.Proof.Seed.CbcScratch
meta import VerifiedGarbage.Proof.Seed.FbScratch
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SEED's wide modes by the AES S-box on x86 (32-bit), without secret residue

The functions as emitted (`Impl.Seed.X86.AesNiWide.Fn`): each runs with its
working space in a frame on the stack, which it wipes, then zeroes, of the
740 bytes of stack its contract reserves below `esp`, the six doublewords
that the residue analysis (`X86.rtaint`) finds it may leave different in two
runs, the header of that frame, clears the registers a callee may change,
and returns without secret residue (`X86.Scrub.verifiedScrubbedSel`, the
kernel evaluating the analysis of the code with its cleanup:
`taint_decide_ct`). Their postconditions read the memory on return only
within their buffers (`Proof/Seed/CbcScratch.lean` and `FbScratch.lean`,
for any pointer width).
-/

@[expose] public section

namespace VG.Proof.Seed.X86.AesNiWide.Scrub

open VG.X86 VG.X86.Scrub

/-! ## Postconditions -/

theorem cbcDecryptOut (stack : Nat) :
    PostOut (Spec.Seed.cbcDecryptChainedContract X86.abi stack) (Spec.Seed.cbcChainedSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Seed.cbcDecChainedPostOut_local _)

theorem cfbDecryptOut (stack : Nat) : PostOut (Spec.Seed.cfbDecryptContract X86.abi stack) (Spec.Seed.cfbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Seed.cfbDecPostOut_local _)

/-! ## The functions -/

/-- `Spec.Seed.cbcDecryptChainedApi` as emitted (`Impl.Seed.X86.AesNiWide.Fn.cbcDecryptChained`) meets its
contract in constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.AesNiWide.Fn.cbcDecryptChained
      (Spec.Seed.cbcDecryptChainedContract X86.abi 740) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cbcDecryptChainedApi) (W := 740)
    { code := Impl.StackScratch.X86.withStackScratchWiped 736 4 178 Impl.Seed.X86.AesNiWide.cbcDecryptChained
      verified := Proof.Seed.X86.AesNiWide.Modes.cbcDecryptChained_framed }
    Impl.Seed.X86.AesNiWide.Fn.modeWords (cbcDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Seed.cfbDecryptApi` as emitted (`Impl.Seed.X86.AesNiWide.Fn.cfbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.AesNiWide.Fn.cfbDecrypt (Spec.Seed.cfbDecryptContract X86.abi 740) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cfbDecryptApi) (W := 740)
    { code := Impl.StackScratch.X86.withStackScratchWiped 736 4 178 Impl.Seed.X86.AesNiWide.cfbDecrypt
      verified := Proof.Seed.X86.AesNiWide.Modes.cfbDecrypt_framed }
    Impl.Seed.X86.AesNiWide.Fn.modeWords (cfbDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.Seed.X86.AesNiWide.Scrub
