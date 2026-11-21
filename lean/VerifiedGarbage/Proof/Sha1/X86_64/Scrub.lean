module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubSel
public import VerifiedGarbage.Impl.Sha1.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Spec.Sha1.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha1.X86_64.Shared
import VerifiedGarbage.Proof.Sha1.Stream
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Spec.Sha1.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sha1.X86_64.Shared
meta import VerifiedGarbage.Proof.Sha1.Stream
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha1.PostOut
meta import VerifiedGarbage.Proof.Sha1.PostOut

/-!
# `vg_sha1_init` on x86-64, without secret residue

`vg_sha1_init`, followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`), which clears the registers it writes. Its
postcondition reads the memory on return only within the streaming state
(`Stream.repr_congr`). HMAC-SHA1, PBKDF2-HMAC-SHA1 and DSA call its code as
the internal `vg_sha1_init_core` (`Proof.Pbkdf2.Md.X86_64.Sha1.hash`), which
clears what it leaves itself.
-/

@[expose] public section

namespace VG.Proof.Sha1.X86_64

open VG.Spec.Sha1 VG.X86_64 VG.X86_64.Scrub

theorem initOut : PostOut (initContract X86_64.abi) (initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.initPost_out 64)

/-! ## The functions as emitted -/

theorem init_codeSp : (Impl.Sha1.X86_64.Stream.init).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sha1.initApi`'s function as emitted (`Impl.Sha1.X86_64.Fn.init`) meets its contract in
constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed target Impl.Sha1.X86_64.Fn.init (Spec.Sha1.initApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedSel (api := Spec.Sha1.initApi)
    { code := Impl.Sha1.X86_64.Stream.init
      verified := Shared.init
      spSafe := init_codeSp }
    .sse [] initOut (RScrub.pubOk_nil _) (by taint_decide)

theorem init_spSafe : Impl.Sha1.X86_64.Fn.init.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe init_codeSp
end VG.Proof.Sha1.X86_64
