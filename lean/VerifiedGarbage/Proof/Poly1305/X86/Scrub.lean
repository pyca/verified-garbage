module

public import VerifiedGarbage.Proof.Poly1305.X86.Init
public import VerifiedGarbage.Proof.Poly1305.X86.Frame
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Poly1305.X86
import VerifiedGarbage.Proof.Poly1305.Scratch
import VerifiedGarbage.Proof.Poly1305.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Poly1305.X86.Init
meta import VerifiedGarbage.Proof.Poly1305.X86.Frame
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Impl.Poly1305.X86
meta import VerifiedGarbage.Proof.Poly1305.Scratch
meta import VerifiedGarbage.Proof.Poly1305.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Poly1305 on x86 (32-bit), without secret residue

`vg_poly1305_init` calls nothing and has no frame: as emitted
(`Impl.Poly1305.X86.Fn.init`) it clears the registers a callee may change
(`X86.Scrub.verifiedScrubbed`). `vg_poly1305_update` and
`vg_poly1305_finalize` keep their working space in a frame of their own: as
emitted they also zero the stack that frame uses
(`X86.Scrub.verifiedScrubbedAll`), given that their postconditions read the
memory on return only within the buffers (`updateOut`, `finalizeOut`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86.Scrub

open VG.X86 VG.X86.Scrub

theorem updateOut (stack : Nat) :
    PostOut (Spec.Poly1305.updateContract X86.abi stack) (Spec.Poly1305.updateSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Poly1305.updatePostOut_local _)

theorem finalizeOut (stack : Nat) :
    PostOut (Spec.Poly1305.finalizeContract X86.abi stack) (Spec.Poly1305.finalizeSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Poly1305.finalizePostOut_local _)

/-- `vg_poly1305_init`, as emitted. -/
theorem init_scrubbed :
    VerifiedScrubbed target Impl.Poly1305.X86.Fn.init (Spec.Poly1305.initContract X86.abi) 0 :=
  verifiedScrubbed (api := Spec.Poly1305.initApi)
    { code := Impl.Poly1305.X86.init
      verified := Proof.Poly1305.X86.init_verified }

/-- `vg_poly1305_update`, as emitted. -/
theorem update_scrubbed :
    VerifiedScrubbed target Impl.Poly1305.X86.Fn.update (Spec.Poly1305.updateContract X86.abi 680) 0 :=
  verifiedScrubbedAll (api := Spec.Poly1305.updateApi)
    { code := Impl.StackScratch.X86.withStackScratch 156 5 Impl.Poly1305.X86.update
      stack := 680
      verified := Proof.Poly1305.X86.update_framed }
    (updateOut _)

/-- `vg_poly1305_finalize`, as emitted. -/
theorem finalize_scrubbed :
    VerifiedScrubbed target Impl.Poly1305.X86.Fn.finalize (Spec.Poly1305.finalizeContract X86.abi 152) 0 :=
  verifiedScrubbedAll (api := Spec.Poly1305.finalizeApi)
    { code := Impl.StackScratch.X86.withStackScratch 152 4 Impl.Poly1305.X86.finalize
      stack := 152
      verified := Proof.Poly1305.X86.finalize_framed }
    (finalizeOut _)

end VG.Proof.Poly1305.X86.Scrub
