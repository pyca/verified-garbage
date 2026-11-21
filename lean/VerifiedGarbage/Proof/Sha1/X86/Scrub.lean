module

public import VerifiedGarbage.Proof.Sha1.X86.Shared
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
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

The one-shot digest, for every backend, with the stack it and its callees
use zeroed first (`X86.Scrub.verifiedScrubbedAll`), given that its postcondition reads
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
(`Impl.MdStream.X86.Digest`). What the cleanup needs of its code
(`scrubFSide`) follows from its code with a stub for both, `.block []`,
evaluated once here (`digest…_side`), and the backend's `updScrub`, `finScrub` and stacks
(`Fill`, `Proof/Framework/X86/ScrubCall.lean`): no backend's code is
evaluated again. -/

open VG.Impl.MdStream.X86.Digest (digest dframe)
open VG.Proof.Sha1.X86.Variants (Backend)

theorem digestRegOut (stack : Nat) : PostOut (Spec.Sha1.digestContract X86.abi stack) (Spec.Sha1.digestSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha1.digestPost_out 32)

theorem digestReg_side : scrubFSide (digest (Proof.Sha1.X86.Variants.hmacHash "" (.block []) (.block []))) [] (28 + dframe (Proof.Sha1.X86.Variants.hmacHash "" (.block []) (.block []))) = true := by
  lit_decide

theorem digestReg_fill (v : Backend) (hu : calleeSide v.stream.upd 20 = true)
    (hf : calleeSide v.stream.fin 20 = true) :
    Fill 20 (digest (Proof.Sha1.X86.Variants.hmacHash "" (.block []) (.block []))) (digest (Proof.Pbkdf2.Stream.X86.sha1H v.stream)) := by
  fill_calls

/-- What the cleanup needs of `vg_sha1_digest`'s code with the backend `v`. -/
theorem digestReg_scrub (v : Backend) :
    scrubFSide (digest (Proof.Pbkdf2.Stream.X86.sha1H v.stream)) []
      (48 + dframe (Proof.Pbkdf2.Stream.X86.sha1H v.stream)) = true :=
  scrubFSide_of_fill (digestReg_fill v (calleeSide_of_le v.stream.updSU v.updScrub)
    (calleeSide_of_le v.stream.finSU v.finScrub)) digestReg_side
    (by show 28 + dframe (Proof.Sha1.X86.Variants.hmacHash "" (.block []) (.block [])) + 20 ≤ 48 + dframe (Proof.Sha1.X86.Variants.hmacHash "" (.block []) (.block [])) ∧ (48 + dframe (Proof.Sha1.X86.Variants.hmacHash "" (.block []) (.block []))) % 4 = 0; decide)

/-- `vg_sha1_digest` with the backend `v`, as emitted (`Impl.Sha1.X86.Fn.digest`), meets its
contract in constant time and returns without secret residue. -/
theorem digest_scrubbed (v : Backend) :
    VerifiedScrubbed target (Impl.Sha1.X86.Fn.digest (Proof.Pbkdf2.Stream.X86.sha1H v.stream))
      (Spec.Sha1.digestContract X86.abi (48 + dframe (Proof.Pbkdf2.Stream.X86.sha1H v.stream))) 0 :=
  verifiedScrubbedAll (api := Spec.Sha1.digestApi)
    { suffix := v.suffix
      code := digest (Proof.Pbkdf2.Stream.X86.sha1H v.stream)
      stack := 48 + dframe (Proof.Pbkdf2.Stream.X86.sha1H v.stream)
      verified := Proof.MdStream.X86.Digest.sha1_digest v.stream
      spSafe := Proof.MdStream.X86.Digest.sha1_digestSp v.stream }
    (digestRegOut _) (hs := digestReg_scrub v)

/-- No instruction of `vg_sha1_digest` with the backend `v`, as emitted, writes `esp` but
in its frames and calls. -/
theorem digest_spSafe (v : Backend) :
    (Impl.Sha1.X86.Fn.digest (Proof.Pbkdf2.Stream.X86.sha1H v.stream)).all
      (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.MdStream.X86.Digest.sha1_digestSp v.stream)

end VG.Proof.Sha1.X86.Scrub
