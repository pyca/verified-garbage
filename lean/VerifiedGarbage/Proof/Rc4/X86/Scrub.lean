module

public import VerifiedGarbage.Spec.Rc4.Contract
public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.Rc4.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rc4.X86.Frame
import VerifiedGarbage.Proof.Rc4.Scratch
import VerifiedGarbage.Proof.Rc4.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Spec.Rc4.Contract
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Impl.Rc4.X86
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Rc4.X86.Frame
meta import VerifiedGarbage.Proof.Rc4.Scratch
meta import VerifiedGarbage.Proof.Rc4.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# RC4 on x86 (32-bit), without secret residue

`vg_rc4_init` and `vg_rc4_apply` as emitted (`Impl.Rc4.X86.Fn`), each followed
by the zeroing of the stack below `esp` that it uses and the clearing of the
registers a callee may change (`X86.Scrub.verifiedScrubbedAll`). Their postconditions read the memory on
return only within their buffers (`Proof.Rc4.initPostOut_local`,
`Proof.Rc4.applyPostOut_local`).
-/

@[expose] public section

namespace VG.Proof.Rc4.X86.Scrub

open VG.X86 VG.X86.Scrub

/-! ## Postconditions -/

theorem initOut : PostOut (Spec.Rc4.initContract X86.abi 84) (Spec.Rc4.initSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Rc4.initPostOut_local _)

theorem applyOut : PostOut (Spec.Rc4.applyContract X86.abi 84) (Spec.Rc4.applySig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Rc4.applyPostOut_local _)

/-! ## The functions as emitted -/

/-- `Spec.Rc4.initApi` as emitted (`Impl.Rc4.X86.Fn.init`) meets its contract
in constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed X86.target Impl.Rc4.X86.Fn.init (Spec.Rc4.initContract X86.abi 84) 32 :=
  verifiedScrubbedAll (api := Spec.Rc4.initApi)
    { code := Impl.StackScratch.X86.withStackScratch 84 3 Impl.Rc4.X86.init
      verified := Proof.Rc4.X86.init_framed }
    initOut

/-- `Spec.Rc4.applyApi` as emitted (`Impl.Rc4.X86.Fn.apply`) meets its contract
in constant time and returns without secret residue. -/
theorem apply_scrubbed :
    VerifiedScrubbed X86.target Impl.Rc4.X86.Fn.apply (Spec.Rc4.applyContract X86.abi 84) 0 :=
  verifiedScrubbedAll (api := Spec.Rc4.applyApi)
    { code := Impl.StackScratch.X86.withStackScratch 84 3 Impl.Rc4.X86.apply
      verified := Proof.Rc4.X86.apply_framed }
    applyOut

end VG.Proof.Rc4.X86.Scrub
