module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha1.Arm.Shared
public import VerifiedGarbage.Proof.Sha256.Arm.Shared
public import VerifiedGarbage.Proof.Sha512.Arm.Shared
public import VerifiedGarbage.Proof.MdStream.Arm.DigestInstances
public import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
public import VerifiedGarbage.Proof.Sha1.PostOut
public import VerifiedGarbage.Proof.Sha256.PostOut
public import VerifiedGarbage.Proof.Sha512.PostOut
import VerifiedGarbage.Proof.Sha1.Arm.Lit
import VerifiedGarbage.Proof.Sha256.Arm.Lit
import VerifiedGarbage.Proof.Sha512.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sha1.Arm.Shared
meta import VerifiedGarbage.Proof.Sha256.Arm.Shared
meta import VerifiedGarbage.Proof.Sha512.Arm.Shared
meta import VerifiedGarbage.Proof.MdStream.Arm.DigestInstances
meta import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
meta import VerifiedGarbage.Proof.Sha1.PostOut
meta import VerifiedGarbage.Proof.Sha256.PostOut
meta import VerifiedGarbage.Proof.Sha512.PostOut
meta import VerifiedGarbage.Proof.Sha1.Arm.Lit
meta import VerifiedGarbage.Proof.Sha256.Arm.Lit
meta import VerifiedGarbage.Proof.Sha512.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-1 and SHA-2 on ARMv7, without secret residue

`init` writes only the streaming state, and has no frame: it is registered
with `Arm.Scrub.scrubReg`. Every other function keeps its working space in a
frame, the `stack` of its contract: `update` and `finalize` 176 bytes
(SHA-1), 624 (SHA-224, SHA-256) or 1392 (SHA-384, SHA-512 and its
truncations) (`withStackScratch`), and the one-shot `digest` `16 + dbytes`
(`withRegScratchWiped`, and the 16 bytes it pushes around `update`). Each is
registered with `Arm.Scrub.scrubRegF`: its code, then that stack zeroed,
then the registers a callee may change, but the result, and the flags set to
constants.

What `scrubRegF` needs of the code follows from its compression function's
alone, which `lit_decide` evaluates on its literal (`Proof/<Hash>/Arm/Lit.lean`):
the generic `update` and `finalize` (`Impl/MdStream/Arm.lean`) use the stack
only as the compression function does (`update_scrubArm`,
`finalize_scrubArm`), and `digest` adds its frame to what its streaming
functions use (`digest_scrubArm`). Their postconditions read the memory on
return only within their buffers (`Arm.Scrub.PostOut`, from the lemmas of
`Proof/<Hash>/PostOut.lean` that the other targets use).

HMAC, PBKDF2, DSA and Ed25519 call this code under internal names
(`vg_sha256_update_scratch`, …, `Proof/Pbkdf2/Stream/Arm/`), as it is
verified, without the wipe, and so does `digest`.
-/

@[expose] public section

namespace VG.Proof.MdStream.Arm.ShaScrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Modes.Arm

/-! ## The code: its frames, and no indirect call -/

/-- What `scrubRegF` needs of code `c`, with `n` bytes of stack. -/
abbrev ScrubOk (c : Prog isa) (n : Nat) : Prop := armStack c ≤ n ∧ noIcall c = true

theorem update_scrubArm (P : Impl.MdStream.Arm.Params) (name : String) {c : Prog isa} {n : Nat}
    (hc : ScrubOk c n) : ScrubOk (Impl.MdStream.Arm.update P name c) n := by
  simp only [ScrubOk, Impl.MdStream.Arm.update, Impl.MdStream.Arm.updateBody, Impl.MdStream.Arm.fill,
    Impl.MdStream.Arm.compressN, Impl.MdStream.Arm.compressWith, armStack, noIcall, hc.2, Bool.and_true,
    Nat.zero_max, Nat.max_zero, Nat.max_self, and_true] at hc ⊢
  exact hc

theorem finalize_scrubArm (P : Impl.MdStream.Arm.Params) (name : String) {c : Prog isa} {n : Nat}
    (hc : ScrubOk c n) : ScrubOk (Impl.MdStream.Arm.finalize P name c) n := by
  simp only [ScrubOk, Impl.MdStream.Arm.finalize, Impl.MdStream.Arm.finalizeBody,
    Impl.MdStream.Arm.compressAt, Impl.MdStream.Arm.compressWith, armStack, noIcall, hc.2, Bool.and_true,
    Nat.zero_max, Nat.max_zero, Nat.max_self, and_true] at hc ⊢
  exact hc

/-- A stack scratch buffer of `bytes` bytes. -/
theorem withStackScratch_scrubArm {bytes m n : Nat} {c : Prog isa} (hc : ScrubOk c n) :
    ScrubOk (Impl.StackScratch.Arm.withStackScratch bytes m c) (n + bytes) := by
  simp only [ScrubOk, Impl.StackScratch.Arm.withStackScratch, armStack, noIcall, hc.2, Bool.and_true,
    Nat.zero_max, and_true] at hc ⊢
  omega

/-- The one-shot digest, from its streaming functions'. -/
theorem digest_scrubArm (H : Impl.Pbkdf2.Stream.Arm.Hash) (hi : ScrubOk H.initC 0) (hu : ScrubOk H.updC 0)
    (hf : ScrubOk H.finC 0) :
    ScrubOk (Impl.MdStream.Arm.Digest.digest H) (16 + Impl.MdStream.Arm.Digest.dbytes H) := by
  refine withRegScratchWiped_scrubArm (n := 16) ?_
  simp only [ScrubOk, Nat.le_zero] at hi hu hf
  simp only [Impl.MdStream.Arm.Digest.digestMain, Impl.Pbkdf2.Stream.Arm.Hash.callInit,
    Impl.Pbkdf2.Stream.Arm.Hash.callFin, Impl.Pbkdf2.Stream.Arm.copy, armStack, noIcall, hi.1, hi.2, hu.1,
    hu.2, hf.1, hf.2, List.length_cons, List.length_nil, Bool.and_self, and_true]
  decide

theorem sha1_compress : ScrubOk Impl.Sha1.Arm.compress 0 := by lit_decide
theorem sha256_compress : ScrubOk Impl.Sha256.Arm.compress 0 := by lit_decide
theorem sha512_compress : ScrubOk Impl.Sha512.Arm.compress 0 := by lit_decide

theorem sha1_update : ScrubOk Impl.Sha1.Arm.Stream.update 0 := update_scrubArm _ _ sha1_compress
theorem sha1_finalize : ScrubOk Impl.Sha1.Arm.Stream.finalize 0 := finalize_scrubArm _ _ sha1_compress
theorem sha256_update : ScrubOk Impl.Sha256.Arm.Stream.update 0 := update_scrubArm _ _ sha256_compress
theorem sha256_finalize : ScrubOk Impl.Sha256.Arm.Stream.finalize 0 := finalize_scrubArm _ _ sha256_compress
theorem sha512_update : ScrubOk Impl.Sha512.Arm.Stream.update 0 := update_scrubArm _ _ sha512_compress
theorem sha512_finalize : ScrubOk Impl.Sha512.Arm.Stream.finalize 0 := finalize_scrubArm _ _ sha512_compress

/-- `init` is one block. -/
theorem block_scrubArm (is : List Instr) : ScrubOk (.block is) 0 := ⟨Nat.le_refl 0, rfl⟩

theorem frameOk_176 : FrameOk 176 := by decide
theorem frameOk_624 : FrameOk 624 := by decide
theorem frameOk_1392 : FrameOk 1392 := by decide

/-! ## SHA-1 -/

/-- `vg_sha1_init`. -/
def sha1InitReg : Registration Spec.Sha1.initApi Arm.target :=
  scrubReg { code := Impl.Sha1.Arm.Stream.init, verified := Proof.Sha1.Arm.Shared.init } rfl

/-- `vg_sha1_update`. -/
def sha1UpdateReg : Registration Spec.Sha1.updateApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 176 2 Impl.Sha1.Arm.Stream.update
      verified := Proof.Sha1.Arm.Shared.update }
    (withStackScratch_scrubArm sha1_update).1 (withStackScratch_scrubArm sha1_update).2 frameOk_176
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.updatePost_out _)) rfl

/-- `vg_sha1_finalize`. -/
def sha1FinalizeReg : Registration Spec.Sha1.finalizeApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 176 1 Impl.Sha1.Arm.Stream.finalize
      verified := Proof.Sha1.Arm.Shared.finalize }
    (withStackScratch_scrubArm sha1_finalize).1 (withStackScratch_scrubArm sha1_finalize).2 frameOk_176
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.finalizePost_out _)) rfl

theorem sha1_digest : ScrubOk (Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha1H)
    (16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha1H) :=
  digest_scrubArm _ (block_scrubArm _) sha1_update sha1_finalize

/-- `vg_sha1_digest`. -/
def sha1DigestReg : Registration Spec.Sha1.digestApi Arm.target :=
  scrubRegF {
      code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha1H
      verified := Proof.MdStream.Arm.Digest.sha1_digest }
    sha1_digest.1 sha1_digest.2 (by decide)
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.digestPost_out _)) rfl

/-! ## SHA-224 and SHA-256 -/

/-- `vg_sha224_init`. -/
def sha224InitReg : Registration Spec.Sha256.init224Api Arm.target :=
  scrubReg { code := Impl.Sha256.Arm.Stream.init224, verified := Proof.Sha256.Arm.Shared.init224 } rfl

/-- `vg_sha256_init`. -/
def sha256InitReg : Registration Spec.Sha256.initApi Arm.target :=
  scrubReg { code := Impl.Sha256.Arm.Stream.init, verified := Proof.Sha256.Arm.Shared.init } rfl

/-- `vg_sha256_update`, which SHA-224 shares. -/
def sha256UpdateReg : Registration Spec.Sha256.updateApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 624 2 Impl.Sha256.Arm.Stream.update
      verified := Proof.Sha256.Arm.Shared.update }
    (withStackScratch_scrubArm sha256_update).1 (withStackScratch_scrubArm sha256_update).2 frameOk_624
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.updatePost_out _)) rfl

/-- `vg_sha256_finalize`. -/
def sha256FinalizeReg : Registration Spec.Sha256.finalizeApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 624 1 Impl.Sha256.Arm.Stream.finalize
      verified := Proof.Sha256.Arm.Shared.finalize }
    (withStackScratch_scrubArm sha256_finalize).1 (withStackScratch_scrubArm sha256_finalize).2 frameOk_624
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalizePost_out _)) rfl

theorem sha224_finalize : ScrubOk Impl.Sha256.Arm.Stream.finalize224 0 :=
  finalize_scrubArm _ _ sha256_compress

/-- `vg_sha224_finalize`. -/
def sha224FinalizeReg : Registration Spec.Sha256.finalize224Api Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 624 1 Impl.Sha256.Arm.Stream.finalize224
      verified := Proof.Sha256.Arm.Shared.finalize224 }
    (withStackScratch_scrubArm sha224_finalize).1 (withStackScratch_scrubArm sha224_finalize).2 frameOk_624
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalize224Post_out _)) rfl

theorem sha224_digest : ScrubOk (Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha224H)
    (16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha224H) :=
  digest_scrubArm _ (block_scrubArm _) sha256_update sha256_finalize

theorem sha256_digest : ScrubOk (Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha256H)
    (16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha256H) :=
  digest_scrubArm _ (block_scrubArm _) sha256_update sha256_finalize

/-- `vg_sha224_digest`. -/
def sha224DigestReg : Registration Spec.Sha256.digest224Api Arm.target :=
  scrubRegF {
      code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha224H
      verified := Proof.MdStream.Arm.Digest.sha224_digest }
    sha224_digest.1 sha224_digest.2 (by decide)
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha256.digestPost_out 28 Spec.Sha256.sha224 _ (by decide))) rfl

/-- `vg_sha256_digest`. -/
def sha256DigestReg : Registration Spec.Sha256.digest256Api Arm.target :=
  scrubRegF {
      code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha256H
      verified := Proof.MdStream.Arm.Digest.sha256_digest }
    sha256_digest.1 sha256_digest.2 (by decide)
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha256.digestPost_out 32 Spec.Sha256.hash _ (by decide))) rfl

/-! ## SHA-384, SHA-512, SHA-512/224 and SHA-512/256 -/

/-- `vg_sha384_init`. -/
def sha384InitReg : Registration Spec.Sha512.init384Api Arm.target :=
  scrubReg {
      code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_384
      verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_384 }
    rfl

/-- `vg_sha512_init`. -/
def sha512InitReg : Registration Spec.Sha512.init512Api Arm.target :=
  scrubReg {
      code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512
      verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512 }
    rfl

/-- `vg_sha512_224_init`. -/
def sha512_224InitReg : Registration Spec.Sha512.init512_224Api Arm.target :=
  scrubReg {
      code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_224
      verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_224 }
    rfl

/-- `vg_sha512_256_init`. -/
def sha512_256InitReg : Registration Spec.Sha512.init512_256Api Arm.target :=
  scrubReg {
      code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_256
      verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_256 }
    rfl

/-- `vg_sha512_update`, which the truncations share. -/
def sha512UpdateReg : Registration Spec.Sha512.updateApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 1392 2 Impl.Sha512.Arm.Stream.update
      verified := Proof.Sha512.Arm.Shared.update }
    (withStackScratch_scrubArm sha512_update).1 (withStackScratch_scrubArm sha512_update).2 frameOk_1392
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.updatePost_out _)) rfl

/-- `vg_sha512_finalize`. -/
def sha512FinalizeReg : Registration Spec.Sha512.finalizeApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 1392 1 Impl.Sha512.Arm.Stream.finalize
      verified := Proof.Sha512.Arm.Shared.finalize }
    (withStackScratch_scrubArm sha512_finalize).1 (withStackScratch_scrubArm sha512_finalize).2 frameOk_1392
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizePost_out _)) rfl

theorem finalizeDigest_scrubArm (P : Impl.MdStream.Arm.Params) :
    ScrubOk (Impl.StackScratch.Arm.withStackScratch 1392 1 (Impl.Sha512.Arm.Stream.finalizeDigest P)) 1392 :=
  withStackScratch_scrubArm (n := 0) (finalize_scrubArm _ _ sha512_compress)

/-- `vg_sha384_finalize`. -/
def sha384FinalizeReg : Registration Spec.Sha512.finalize384Api Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 1392 1
        (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params384)
      verified := Proof.Sha512.Arm.Shared.finalize384 }
    (finalizeDigest_scrubArm _).1 (finalizeDigest_scrubArm _).2 frameOk_1392
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.finalizeDigestPost_out Spec.Sha512.H0_384 48 Spec.Sha512.sha384 _ (by decide))) rfl

/-- `vg_sha512_256_finalize`. -/
def sha512_256FinalizeReg : Registration Spec.Sha512.finalize512_256Api Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 1392 1
        (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_256)
      verified := Proof.Sha512.Arm.Shared.finalize512_256 }
    (finalizeDigest_scrubArm _).1 (finalizeDigest_scrubArm _).2 frameOk_1392
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.finalizeDigestPost_out Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256 _ (by decide))) rfl

/-- `vg_sha512_224_finalize`. -/
def sha512_224FinalizeReg : Registration Spec.Sha512.finalize512_224Api Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 1392 1
        (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_224)
      verified := Proof.Sha512.Arm.Shared.finalize512_224 }
    (finalizeDigest_scrubArm _).1 (finalizeDigest_scrubArm _).2 frameOk_1392
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.finalizeDigestPost_out Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224 _ (by decide))) rfl

theorem sha384_digest : ScrubOk (Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha384H)
    (16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha384H) :=
  digest_scrubArm _ (block_scrubArm _) sha512_update sha512_finalize

theorem sha512_digest : ScrubOk (Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512H')
    (16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha512H') :=
  digest_scrubArm _ (block_scrubArm _) sha512_update sha512_finalize

theorem sha512_224_digest : ScrubOk (Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512_224H)
    (16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha512_224H) :=
  digest_scrubArm _ (block_scrubArm _) sha512_update sha512_finalize

theorem sha512_256_digest : ScrubOk (Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512_256H)
    (16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha512_256H) :=
  digest_scrubArm _ (block_scrubArm _) sha512_update sha512_finalize

/-- `vg_sha384_digest`. -/
def sha384DigestReg : Registration Spec.Sha512.digest384Api Arm.target :=
  scrubRegF {
      code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha384H
      verified := Proof.MdStream.Arm.Digest.sha384_digest }
    sha384_digest.1 sha384_digest.2 (by decide)
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.digestPost_out 48 Spec.Sha512.sha384 _ (by decide))) rfl

/-- `vg_sha512_digest`. -/
def sha512DigestReg : Registration Spec.Sha512.digest512Api Arm.target :=
  scrubRegF {
      code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512H'
      verified := Proof.MdStream.Arm.Digest.sha512_digest }
    sha512_digest.1 sha512_digest.2 (by decide)
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.digestPost_out 64 Spec.Sha512.sha512 _ (by decide))) rfl

/-- `vg_sha512_224_digest`. -/
def sha512_224DigestReg : Registration Spec.Sha512.digest512_224Api Arm.target :=
  scrubRegF {
      code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512_224H
      verified := Proof.MdStream.Arm.Digest.sha512_224_digest }
    sha512_224_digest.1 sha512_224_digest.2 (by decide)
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.digestPost_out 28 Spec.Sha512.sha512_224 _ (by decide))) rfl

/-- `vg_sha512_256_digest`. -/
def sha512_256DigestReg : Registration Spec.Sha512.digest512_256Api Arm.target :=
  scrubRegF {
      code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512_256H
      verified := Proof.MdStream.Arm.Digest.sha512_256_digest }
    sha512_256_digest.1 sha512_256_digest.2 (by decide)
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.digestPost_out 32 Spec.Sha512.sha512_256 _ (by decide))) rfl

end VG.Proof.MdStream.Arm.ShaScrub
