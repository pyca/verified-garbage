module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Md5
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha1
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha224
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha256
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_224
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_256
public import VerifiedGarbage.Proof.Hmac.AnyKey
public import VerifiedGarbage.Proof.Hmac.Scratch
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# HMAC on PPC64LE, without secret residue

Each hash's HMAC `init` and `finalize`, followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.withScrub`), which clears the
volatile registers and the stack its frames used: both keep their working
space in a frame they do not wipe themselves (`withStackScratch`), and
`init` calls the hash's compression function, which pushes frames of its own.
Their postconditions read the memory on return only within their buffers, by
RISC-V's proofs (`Proof/Hmac/Stream/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-- HMAC's `init`'s postcondition reads the memory on return only within the
inner and outer states. -/
theorem hmacInitAnyOut (I : Spec.Hmac.Instance) (hR : Proof.Hmac.ReprLocal I.S) (hS : I.S.stateBytes < 2 ^ 64)
    (stack : Nat) : PostOut (I.initAnyKeyContract abi stack) ((Spec.Hmac.initSig I.S).retBits 64) := by
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
  exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Hmac.initPostOut_local I.S _ hR hS)

/-- HMAC's `finalize`'s postcondition reads the memory on return only within
`out`, the HMAC's bytes. -/
theorem hmacFinOut (I : Spec.Hmac.Instance) (hD : I.S.digestBytes < 2 ^ 64) (stack : Nat) :
    PostOut (I.finalizeContract abi stack) ((Spec.Hmac.finalizeSig I.S).retBits 64) := by
  unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨inn, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨otr, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Hmac.finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have ho : ∀ i < I.S.digestBytes, m₂ (out + BitVec.ofNat 64 i) = m₁ (out + BitVec.ofNat 64 i) :=
      fun i hi => (hb.2.2 _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hD, hi]))).symm
    intro k0 text h1 h2 hri hc hro
    show Spec.Sha256.bytesAt m₂ out I.S.digestBytes = _
    rw [Sha256.Stream.bytesAt_congr ho]
    exact h k0 text h1 h2 hri hc hro

/-- `Spec.Hmac.md5I.initAnyKeyApi`. -/
def md5InitAnyKeyReg : Registration Spec.Hmac.md5I.initAnyKeyApi PPC64LE.target :=
  withScrub {
      code := initCode Md5.hash Spec.Hmac.md5I 6
      verified := Md5.initAny }
    (hmacInitAnyOut Spec.Hmac.md5I Proof.Hmac.md5_local (by decide) _)

/-- `Spec.Hmac.md5I.finalizeApi`. -/
def md5FinalizeReg : Registration Spec.Hmac.md5I.finalizeApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.md5I) .r7 Md5.hash.finalize
      verified := Md5.finalize }
    (hmacFinOut Spec.Hmac.md5I (by decide) _)

/-- `Spec.Hmac.sha1I.initAnyKeyApi`. -/
def sha1InitAnyKeyReg : Registration Spec.Hmac.sha1I.initAnyKeyApi PPC64LE.target :=
  withScrub {
      code := initCode Sha1.hash Spec.Hmac.sha1I 6
      verified := Sha1.initAny }
    (hmacInitAnyOut Spec.Hmac.sha1I Proof.Hmac.sha1_local (by decide) _)

/-- `Spec.Hmac.sha1I.finalizeApi`. -/
def sha1FinalizeReg : Registration Spec.Hmac.sha1I.finalizeApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha1I) .r7 Sha1.hash.finalize
      verified := Sha1.finalize }
    (hmacFinOut Spec.Hmac.sha1I (by decide) _)

/-- `Spec.Hmac.sha224I.initAnyKeyApi`. -/
def sha224InitAnyKeyReg : Registration Spec.Hmac.sha224I.initAnyKeyApi PPC64LE.target :=
  withScrub {
      code := initCode Sha224.hash Spec.Hmac.sha224I 6
      verified := Sha224.initAny }
    (hmacInitAnyOut Spec.Hmac.sha224I Proof.Hmac.sha224_local (by decide) _)

/-- `Spec.Hmac.sha224I.finalizeApi`. -/
def sha224FinalizeReg : Registration Spec.Hmac.sha224I.finalizeApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha224I) .r7 Sha224.hash.finalize
      verified := Sha224.finalize }
    (hmacFinOut Spec.Hmac.sha224I (by decide) _)

/-- `Spec.Hmac.sha256I.initAnyKeyApi`. -/
def sha256InitAnyKeyReg : Registration Spec.Hmac.sha256I.initAnyKeyApi PPC64LE.target :=
  withScrub {
      code := initCode Sha256.hash Spec.Hmac.sha256I 6
      verified := Sha256.initAny }
    (hmacInitAnyOut Spec.Hmac.sha256I Proof.Hmac.sha256_local (by decide) _)

/-- `Spec.Hmac.sha256I.finalizeApi`. -/
def sha256FinalizeReg : Registration Spec.Hmac.sha256I.finalizeApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha256I) .r7 Sha256.hash.finalize
      verified := Sha256.finalize }
    (hmacFinOut Spec.Hmac.sha256I (by decide) _)

/-- `Spec.Hmac.sha384I.initAnyKeyApi`. -/
def sha384InitAnyKeyReg : Registration Spec.Hmac.sha384I.initAnyKeyApi PPC64LE.target :=
  withScrub {
      code := initCode Sha384.hash Spec.Hmac.sha384I 7
      verified := Sha384.initAny }
    (hmacInitAnyOut Spec.Hmac.sha384I Proof.Hmac.sha384_local (by decide) _)

/-- `Spec.Hmac.sha384I.finalizeApi`. -/
def sha384FinalizeReg : Registration Spec.Hmac.sha384I.finalizeApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha384I) .r7 Sha384.hash.finalize
      verified := Sha384.finalize }
    (hmacFinOut Spec.Hmac.sha384I (by decide) _)

/-- `Spec.Hmac.sha512I.initAnyKeyApi`. -/
def sha512InitAnyKeyReg : Registration Spec.Hmac.sha512I.initAnyKeyApi PPC64LE.target :=
  withScrub {
      code := initCode Sha512.hash Spec.Hmac.sha512I 7
      verified := Sha512.initAny }
    (hmacInitAnyOut Spec.Hmac.sha512I Proof.Hmac.sha512_local (by decide) _)

/-- `Spec.Hmac.sha512I.finalizeApi`. -/
def sha512FinalizeReg : Registration Spec.Hmac.sha512I.finalizeApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha512I) .r7 Sha512.hash.finalize
      verified := Sha512.finalize }
    (hmacFinOut Spec.Hmac.sha512I (by decide) _)

/-- `Spec.Hmac.sha512_224I.initAnyKeyApi`. -/
def sha512_224InitAnyKeyReg : Registration Spec.Hmac.sha512_224I.initAnyKeyApi PPC64LE.target :=
  withScrub {
      code := initCode Sha512_224.hash Spec.Hmac.sha512_224I 7
      verified := Sha512_224.initAny }
    (hmacInitAnyOut Spec.Hmac.sha512_224I Proof.Hmac.sha512_224_local (by decide) _)

/-- `Spec.Hmac.sha512_224I.finalizeApi`. -/
def sha512_224FinalizeReg : Registration Spec.Hmac.sha512_224I.finalizeApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha512_224I) .r7 Sha512_224.hash.finalize
      verified := Sha512_224.finalize }
    (hmacFinOut Spec.Hmac.sha512_224I (by decide) _)

/-- `Spec.Hmac.sha512_256I.initAnyKeyApi`. -/
def sha512_256InitAnyKeyReg : Registration Spec.Hmac.sha512_256I.initAnyKeyApi PPC64LE.target :=
  withScrub {
      code := initCode Sha512_256.hash Spec.Hmac.sha512_256I 7
      verified := Sha512_256.initAny }
    (hmacInitAnyOut Spec.Hmac.sha512_256I Proof.Hmac.sha512_256_local (by decide) _)

/-- `Spec.Hmac.sha512_256I.finalizeApi`. -/
def sha512_256FinalizeReg : Registration Spec.Hmac.sha512_256I.finalizeApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha512_256I) .r7 Sha512_256.hash.finalize
      verified := Sha512_256.finalize }
    (hmacFinOut Spec.Hmac.sha512_256I (by decide) _)

/-- All are scrubbed: the side conditions of `withScrub` hold. MD5's and
SHA-1's code is too long for `decide` (it reaches the recursion limit): the
emitter checks theirs, refusing a function `ci/residue_allowlist.txt` does not
list whose registration has no `residue`. -/
example : sha224InitAnyKeyReg.residue.isSome ∧ sha224FinalizeReg.residue.isSome := by decide
example : sha256InitAnyKeyReg.residue.isSome ∧ sha256FinalizeReg.residue.isSome := by decide
example : sha384InitAnyKeyReg.residue.isSome ∧ sha384FinalizeReg.residue.isSome := by decide
example : sha512InitAnyKeyReg.residue.isSome ∧ sha512FinalizeReg.residue.isSome := by decide
example : sha512_224InitAnyKeyReg.residue.isSome ∧ sha512_224FinalizeReg.residue.isSome := by decide
example : sha512_256InitAnyKeyReg.residue.isSome ∧ sha512_256FinalizeReg.residue.isSome := by decide

end VG.Proof.Hmac.Stream.PPC64LE.Scrub
