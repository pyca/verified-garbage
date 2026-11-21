module

public import VerifiedGarbage.Proof.Md5.X86.Shared
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Md5.Contract
public import VerifiedGarbage.Impl.Md5.X86.Stream
import VerifiedGarbage.Proof.Md5.PostOut
import VerifiedGarbage.Proof.Md5.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Md5.X86.Shared
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Md5.Contract
meta import VerifiedGarbage.Impl.Md5.X86.Stream
meta import VerifiedGarbage.Proof.Md5.PostOut
meta import VerifiedGarbage.Proof.Md5.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# MD5's streaming functions on x86 (32-bit), without secret residue

The functions as emitted (`Impl.Md5.X86.Fn`): `vg_md5_init`, which calls
nothing and has no frame, followed by the clearing of the registers a callee
may change (`X86.Scrub.verifiedScrubbed`); `vg_md5_update` and
`vg_md5_finalize`, whose working space is in a frame of their own, with the
stack they and the compression function use zeroed first
(`X86.Scrub.verifiedScrubbedAll`), given that their postconditions read the
memory on return only within the buffers (`Proof.Md5.PostOut`). HMAC-MD5 and
PBKDF2-HMAC-MD5 call `vg_md5_init`'s code as the internal `vg_md5_init_core`
(`Proof.Pbkdf2.Stream.X86.md5H`).
-/

@[expose] public section

namespace VG.Proof.Md5.X86.Scrub

open VG.Spec.Md5 VG.X86 VG.X86.Scrub

theorem updateOut (stack : Nat) : PostOut (updateContract X86.abi stack) (updateSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Md5.updatePost_out 32)

theorem finalizeOut (stack : Nat) : PostOut (finalizeContract X86.abi stack) (finalizeSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Md5.finalizePost_out 32)

/-- `vg_md5_init` as emitted (`Impl.Md5.X86.Fn.init`) meets its contract in constant
time and returns without secret residue. -/
theorem init_scrubbed : VerifiedScrubbed target Impl.Md5.X86.Fn.init (initContract X86.abi) 0 :=
  verifiedScrubbed (api := Spec.Md5.initApi) { code := Impl.Md5.X86.Stream.init, verified := Shared.init }

/-- `vg_md5_update` as emitted (`Impl.Md5.X86.Fn.update`) meets its contract in constant
time and returns without secret residue. -/
theorem update_scrubbed :
    VerifiedScrubbed target Impl.Md5.X86.Fn.update (updateContract X86.abi (20 + 140)) 0 :=
  verifiedScrubbedAll (api := Spec.Md5.updateApi)
    { code := Impl.StackScratch.X86.withStackScratch 140 5 Impl.Md5.X86.Stream.update
      stack := 20 + 140
      verified := Shared.update }
    (updateOut _)

/-- `vg_md5_finalize` as emitted (`Impl.Md5.X86.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_scrubbed :
    VerifiedScrubbed target Impl.Md5.X86.Fn.finalize (finalizeContract X86.abi (20 + 136)) 0 :=
  verifiedScrubbedAll (api := Spec.Md5.finalizeApi)
    { code := Impl.StackScratch.X86.withStackScratch 136 4 Impl.Md5.X86.Stream.finalize
      stack := 20 + 136
      verified := Shared.finalize }
    (finalizeOut _)

end VG.Proof.Md5.X86.Scrub
