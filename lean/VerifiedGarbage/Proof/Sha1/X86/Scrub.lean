module

public import VerifiedGarbage.Proof.Sha1.X86.Shared
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Impl.Sha1.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
public import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
public import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Proof.Sha1.X86.Lit
import VerifiedGarbage.Proof.Sha1.PostOut
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha1.X86.Shared
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Impl.Sha1.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
meta import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
meta import VerifiedGarbage.Spec.Sha1.Contract
meta import VerifiedGarbage.Proof.Sha1.X86.Lit
meta import VerifiedGarbage.Proof.Sha1.PostOut
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-1's `init` and one-shot digest on x86 (32-bit), without secret residue

`vg_sha1_init`, which calls nothing and has no frame, followed by the
clearing of the registers a callee may change (`X86.Scrub.verifiedScrubbed`). HMAC,
PBKDF2 and the one-shot digest call its code as the internal
`vg_sha1_init_core` (`Variants.hmacHash`), whose code is not scrubbed.

The one-shot digest, for every backend, with the doublewords of the stack it
and its callees may leave secret zeroed first (`X86.Scrub.SelScrub.scrubbed`), given that its postcondition reads
the memory on return only within the buffers (`Proof.Sha1.PostOut`). The
streaming `update` and `finalize` are scrubbed where each backend defines
them (`Variants.Backend.update_scrubbed`, …).
-/

@[expose] public section

namespace VG.Proof.Sha1.X86.Scrub

open VG.X86 VG.X86.Scrub

/-- `vg_sha1_init` as emitted (`Impl.Sha1.X86.Fn.init`) meets its contract in constant time
and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed target Impl.Sha1.X86.Fn.init (Spec.Sha1.initContract X86.abi) 0 :=
  verifiedScrubbed (api := Spec.Sha1.initApi)
    { code := Impl.Sha1.X86.Stream.init, verified := Proof.Sha1.X86.Shared.init }

/-! ## The one-shot digests, for every backend

A digest calls the backend's streaming `update` and `finalize`
(`Impl.MdStream.X86.Digest`), and is followed by the zeroing of only the
doublewords the residue analysis finds it may leave different in two runs
(`Impl.MdStream.X86.Digest.selWords`, `X86.Scrub.SelScrub.scrubbed`). The
analysis of its code with a backend is evaluated where the backend is
defined, once (`Backend.digestSel`, …): no backend's code is evaluated
again here. -/

open VG.Impl.MdStream.X86.Digest (digest dframe)
open VG.Proof.Sha1.X86.Variants (Backend)

theorem digestRegOut (stack : Nat) : PostOut (Spec.Sha1.digestContract X86.abi stack) (Spec.Sha1.digestSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha1.digestPost_out 32)

/-- `vg_sha1_digest` with the backend `v`, as emitted (`Impl.Sha1.X86.Fn.digest`), meets its
contract in constant time and returns without secret residue. -/
theorem digest_scrubbed (v : Backend) :
    VerifiedScrubbed target (Impl.Sha1.X86.Fn.digest (Proof.Pbkdf2.Stream.X86.sha1H v.stream))
      (Spec.Sha1.digestContract X86.abi (48 + dframe (Proof.Pbkdf2.Stream.X86.sha1H v.stream))) 0 :=
  SelScrub.scrubbed (api := Spec.Sha1.digestApi)
    { suffix := v.suffix
      code := digest (Proof.Pbkdf2.Stream.X86.sha1H v.stream)
      stack := 48 + dframe (Proof.Pbkdf2.Stream.X86.sha1H v.stream)
      verified := Proof.MdStream.X86.Digest.sha1_digest v.stream
      spSafe := Proof.MdStream.X86.Digest.sha1_digestSp v.stream }
    v.digestSel (digestRegOut _)

/-- No instruction of `vg_sha1_digest` with the backend `v`, as emitted, writes `esp` but
in its frames and calls. -/
theorem digest_spSafe (v : Backend) :
    (Impl.Sha1.X86.Fn.digest (Proof.Pbkdf2.Stream.X86.sha1H v.stream)).all
      (fun i => !isa.writesSp i) = true :=
  scrubSel_spSafe (Proof.MdStream.X86.Digest.sha1_digestSp v.stream)

end VG.Proof.Sha1.X86.Scrub
