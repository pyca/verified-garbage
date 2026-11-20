module

public import VerifiedGarbage.Proof.Sha256.X86.Shared
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.Sha256.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
public import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Sha256.PostOut
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha256.X86.Shared
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.Sha256.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
meta import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
meta import VerifiedGarbage.Spec.Sha256.Contract
meta import VerifiedGarbage.Proof.Sha256.X86.Lit
meta import VerifiedGarbage.Proof.Sha256.PostOut
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-224's and SHA-256's `init` and one-shot digests on x86 (32-bit), without secret residue

The `init`s of SHA-224 and SHA-256, which call nothing and have no frame,
each followed by the clearing of the registers a callee may change
(`X86.Scrub.verifiedScrubbed`). HMAC, PBKDF2, RSA and the one-shot digests call their
code as the internal `vg_sha224_init_core` and `vg_sha256_init_core`
(`Variants.hmacHash`), whose code is not scrubbed.

The one-shot digests, for every backend, with the stack they and their
callees use zeroed first (`X86.Scrub.verifiedScrubbedF`), given that their
postconditions read the memory on return only within the buffers
(`Proof.Sha256.PostOut`). The streaming `update` and `finalize` are scrubbed
where each backend defines them (`Variants.StreamFn.reg`).
-/

@[expose] public section

namespace VG.Proof.Sha256.X86.Scrub

open VG.X86 VG.X86.Scrub

/-- `vg_sha224_init` as emitted (`Impl.Sha256.X86.Fn.init224`) meets its contract in
constant time and returns without secret residue. -/
theorem init224_scrubbed :
    VerifiedScrubbed target Impl.Sha256.X86.Fn.init224 (Spec.Sha256.init224Contract X86.abi) 0 :=
  verifiedScrubbed (api := Spec.Sha256.init224Api)
    { code := Impl.Sha256.X86.Stream.init224, verified := Proof.Sha256.X86.Shared.init224 }

/-- `vg_sha256_init` as emitted (`Impl.Sha256.X86.Fn.init`) meets its contract in constant
time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed target Impl.Sha256.X86.Fn.init (Spec.Sha256.initContract X86.abi) 0 :=
  verifiedScrubbed (api := Spec.Sha256.initApi)
    { code := Impl.Sha256.X86.Stream.init, verified := Proof.Sha256.X86.Shared.init }

/-! ## The one-shot digests, for every backend

A digest calls the backend's streaming `update` and `finalize`
(`Impl.MdStream.X86.Digest`). What `scrubFOf` needs of its code follows from
its code with a stub for both, `.block []`, evaluated once here
(`digest…_side`), and the backend's `updScrub`, `finScrub` and stacks
(`Fill`, `Proof/Framework/X86/ScrubCall.lean`): no backend's code is
evaluated again. -/

open VG.Impl.MdStream.X86.Digest (digest dframe)
open VG.Proof.Sha256.X86.Variants (Backend)

theorem digestRegOut (stack : Nat) : PostOut (Spec.Sha256.digestContract X86.abi 32 Spec.Sha256.hash stack) ((Spec.Sha256.digestSig 32).retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha256.digestPost_out 32 Spec.Sha256.hash 32 (by decide))

theorem digestReg_side : scrubFSide (digest (Proof.Sha256.X86.Variants.hmacHash "" (.block []) (.block []))) [] (28 + dframe (Proof.Sha256.X86.Variants.hmacHash "" (.block []) (.block []))) = true := by
  lit_decide

theorem digestReg_fill (v : Backend) (hu : calleeSide v.stream.upd 20 = true)
    (hf : calleeSide v.stream.fin 20 = true) :
    Fill 20 (digest (Proof.Sha256.X86.Variants.hmacHash "" (.block []) (.block []))) (digest (Proof.Pbkdf2.Stream.X86.sha256H v.stream)) := by
  fill_calls

/-- What `scrubFOf` needs of `vg_sha256_digest`'s code with the backend `v`. -/
theorem digestReg_scrub (v : Backend) :
    scrubFSide (digest (Proof.Pbkdf2.Stream.X86.sha256H v.stream)) []
      (48 + dframe (Proof.Pbkdf2.Stream.X86.sha256H v.stream)) = true :=
  scrubFSide_of_fill (digestReg_fill v (calleeSide_of_le v.stream.updSU v.updScrub)
    (calleeSide_of_le v.stream.finSU v.finScrub)) digestReg_side
    (by show 28 + dframe (Proof.Sha256.X86.Variants.hmacHash "" (.block []) (.block [])) + 20 ≤ 48 + dframe (Proof.Sha256.X86.Variants.hmacHash "" (.block []) (.block [])) ∧ (48 + dframe (Proof.Sha256.X86.Variants.hmacHash "" (.block []) (.block []))) % 4 = 0; decide)

/-- `vg_sha256_digest` with the backend `v`, as emitted (`Impl.Sha256.X86.Fn.digest`),
meets its contract in constant time and returns without secret residue. -/
theorem digest_scrubbed (v : Backend) :
    VerifiedScrubbed target (Impl.Sha256.X86.Fn.digest (Proof.Pbkdf2.Stream.X86.sha256H v.stream))
      (Spec.Sha256.digestContract X86.abi 32 Spec.Sha256.hash (48 + dframe (Proof.Pbkdf2.Stream.X86.sha256H v.stream))) 0 :=
  verifiedScrubbedF (api := Spec.Sha256.digest256Api)
    { suffix := v.suffix
      code := digest (Proof.Pbkdf2.Stream.X86.sha256H v.stream)
      stack := 48 + dframe (Proof.Pbkdf2.Stream.X86.sha256H v.stream)
      verified := Proof.MdStream.X86.Digest.sha256_digest v.stream
      spSafe := Proof.MdStream.X86.Digest.sha256_digestSp v.stream }
    (digestRegOut _) (hs := digestReg_scrub v)

/-- No instruction of `vg_sha256_digest` with the backend `v`, as emitted, writes `esp`
but in its frames and calls. -/
theorem digest_spSafe (v : Backend) :
    (Impl.Sha256.X86.Fn.digest (Proof.Pbkdf2.Stream.X86.sha256H v.stream)).all
      (fun i => !isa.writesSp i) = true :=
  scrubF_spSafe (Proof.MdStream.X86.Digest.sha256_digestSp v.stream)

theorem digest224RegOut (stack : Nat) : PostOut (Spec.Sha256.digestContract X86.abi 28 Spec.Sha256.sha224 stack) ((Spec.Sha256.digestSig 28).retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha256.digestPost_out 28 Spec.Sha256.sha224 32 (by decide))

theorem digest224Reg_side : scrubFSide (digest (Proof.Sha256.X86.Variants.hmacHash224 "" (.block []) (.block []))) [] (28 + dframe (Proof.Sha256.X86.Variants.hmacHash224 "" (.block []) (.block []))) = true := by
  lit_decide

theorem digest224Reg_fill (v : Backend) (hu : calleeSide v.stream.upd 20 = true)
    (hf : calleeSide v.stream.fin 20 = true) :
    Fill 20 (digest (Proof.Sha256.X86.Variants.hmacHash224 "" (.block []) (.block []))) (digest (Proof.Pbkdf2.Stream.X86.sha224H v.stream)) := by
  fill_calls

/-- What `scrubFOf` needs of `vg_sha224_digest`'s code with the backend `v`. -/
theorem digest224Reg_scrub (v : Backend) :
    scrubFSide (digest (Proof.Pbkdf2.Stream.X86.sha224H v.stream)) []
      (48 + dframe (Proof.Pbkdf2.Stream.X86.sha224H v.stream)) = true :=
  scrubFSide_of_fill (digest224Reg_fill v (calleeSide_of_le v.stream.updSU v.updScrub)
    (calleeSide_of_le v.stream.finSU v.finScrub)) digest224Reg_side
    (by show 28 + dframe (Proof.Sha256.X86.Variants.hmacHash224 "" (.block []) (.block [])) + 20 ≤ 48 + dframe (Proof.Sha256.X86.Variants.hmacHash224 "" (.block []) (.block [])) ∧ (48 + dframe (Proof.Sha256.X86.Variants.hmacHash224 "" (.block []) (.block []))) % 4 = 0; decide)

/-- `vg_sha224_digest` with the backend `v`, as emitted (`Impl.Sha256.X86.Fn.digest`),
meets its contract in constant time and returns without secret residue. -/
theorem digest224_scrubbed (v : Backend) :
    VerifiedScrubbed target (Impl.Sha256.X86.Fn.digest (Proof.Pbkdf2.Stream.X86.sha224H v.stream))
      (Spec.Sha256.digestContract X86.abi 28 Spec.Sha256.sha224 (48 + dframe (Proof.Pbkdf2.Stream.X86.sha224H v.stream))) 0 :=
  verifiedScrubbedF (api := Spec.Sha256.digest224Api)
    { suffix := v.suffix
      code := digest (Proof.Pbkdf2.Stream.X86.sha224H v.stream)
      stack := 48 + dframe (Proof.Pbkdf2.Stream.X86.sha224H v.stream)
      verified := Proof.MdStream.X86.Digest.sha224_digest v.stream
      spSafe := Proof.MdStream.X86.Digest.sha224_digestSp v.stream }
    (digest224RegOut _) (hs := digest224Reg_scrub v)

/-- No instruction of `vg_sha224_digest` with the backend `v`, as emitted, writes `esp`
but in its frames and calls. -/
theorem digest224_spSafe (v : Backend) :
    (Impl.Sha256.X86.Fn.digest (Proof.Pbkdf2.Stream.X86.sha224H v.stream)).all
      (fun i => !isa.writesSp i) = true :=
  scrubF_spSafe (Proof.MdStream.X86.Digest.sha224_digestSp v.stream)

end VG.Proof.Sha256.X86.Scrub
