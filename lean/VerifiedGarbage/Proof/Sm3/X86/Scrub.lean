module

public import VerifiedGarbage.Proof.Sm3.X86.Shared
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Sm3.Contract
public import VerifiedGarbage.Impl.Sm3.X86.Stream
import VerifiedGarbage.Proof.Sm3.PostOut
import VerifiedGarbage.Proof.Sm3.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sm3.X86.Shared
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Sm3.Contract
meta import VerifiedGarbage.Impl.Sm3.X86.Stream
meta import VerifiedGarbage.Proof.Sm3.PostOut
meta import VerifiedGarbage.Proof.Sm3.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM3's streaming functions on x86 (32-bit), without secret residue

The functions as emitted (`Impl.Sm3.X86.Fn`): `vg_sm3_init`, which calls
nothing and has no frame, followed by the clearing of the registers a callee
may change (`X86.Scrub.verifiedScrubbed`); `vg_sm3_update` and
`vg_sm3_finalize`, whose working space is in a frame of their own, with the
stack they and the compression function use zeroed first
(`X86.Scrub.verifiedScrubbedF`), given that their postconditions read the
memory on return only within the buffers (`Proof.Sm3.PostOut`).
-/

@[expose] public section

namespace VG.Proof.Sm3.X86.Scrub

open VG.Spec.Sm3 VG.X86 VG.X86.Scrub

theorem updateOut (stack : Nat) : PostOut (updateContract X86.abi stack) (updateSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sm3.updatePost_out 32)

theorem finalizeOut (stack : Nat) : PostOut (finalizeContract X86.abi stack) (finalizeSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sm3.finalizePost_out 32)

/-- `vg_sm3_init` as emitted (`Impl.Sm3.X86.Fn.init`) meets its contract in constant
time and returns without secret residue. -/
theorem init_scrubbed : VerifiedScrubbed target Impl.Sm3.X86.Fn.init (initContract X86.abi) 0 :=
  verifiedScrubbed (api := Spec.Sm3.initApi) { code := Impl.Sm3.X86.Stream.init, verified := Shared.init }

/-- `vg_sm3_update` as emitted (`Impl.Sm3.X86.Fn.update`) meets its contract in constant
time and returns without secret residue. -/
theorem update_scrubbed :
    VerifiedScrubbed target Impl.Sm3.X86.Fn.update (updateContract X86.abi (20 + 188)) 0 :=
  verifiedScrubbedF (api := Spec.Sm3.updateApi)
    { code := Impl.StackScratch.X86.withStackScratch 188 5 Impl.Sm3.X86.Stream.update
      stack := 20 + 188
      verified := Shared.update }
    (updateOut _)

/-- `vg_sm3_finalize` as emitted (`Impl.Sm3.X86.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_scrubbed :
    VerifiedScrubbed target Impl.Sm3.X86.Fn.finalize (finalizeContract X86.abi (20 + 184)) 0 :=
  verifiedScrubbedF (api := Spec.Sm3.finalizeApi)
    { code := Impl.StackScratch.X86.withStackScratch 184 4 Impl.Sm3.X86.Stream.finalize
      stack := 20 + 184
      verified := Shared.finalize }
    (finalizeOut _)

end VG.Proof.Sm3.X86.Scrub
