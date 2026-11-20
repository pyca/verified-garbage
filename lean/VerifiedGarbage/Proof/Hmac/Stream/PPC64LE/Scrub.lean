module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
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
import VerifiedGarbage.Proof.Framework.Lit

/-!
# HMAC on PPC64LE, without secret residue

Each hash's HMAC `init` and `finalize` as emitted
(`Impl/Hmac/Stream/PPC64LE/Fn.lean`), followed by its cleanup
(`Impl.Scrub.PPC64LE.scrub`, `PPC64LE.Scrub.verifiedScrubbed`), which clears the
volatile registers and the stack its frames used: both keep their working
space in a frame they do not wipe themselves (`withStackScratch`), and
`init` calls the hash's compression function, which pushes frames of its own.
Their postconditions read the memory on return only within their buffers, by
RISC-V's proofs (`Proof/Hmac/Stream/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub
open VG.Impl.Hmac.Stream.PPC64LE (md5Hash sha1Hash sha224Hash sha256Hash sha384Hash sha512Hash
  sha512_224Hash sha512_256Hash hmacFrame initCode)

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

/-- `vg_hmac_md5_init` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.initMd5`) meets its
contract in constant time and returns without secret residue. -/
theorem md5_init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.initMd5
      (Spec.Hmac.md5I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.md5I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.md5I.initAnyKeyApi) {
      code := initCode md5Hash Spec.Hmac.md5I 6
      verified := Md5.initAny }
    512 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (hmacInitAnyOut Spec.Hmac.md5I Proof.Hmac.md5_local (by decide) _)
    (by dsimp only; lit_decide)

/-- `vg_hmac_md5_finalize` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.finalizeMd5`) meets
its contract in constant time and returns without secret residue. -/
theorem md5_finalize_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.finalizeMd5
      (Spec.Hmac.md5I.finalizeContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.md5I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.md5I.finalizeApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.md5I) .r7 md5Hash.finalize
      verified := Md5.finalize }
    512 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (hmacFinOut Spec.Hmac.md5I (by decide) _)
    (by dsimp only; lit_decide)

/-- `vg_hmac_sha1_init` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.initSha1`) meets its
contract in constant time and returns without secret residue. -/
theorem sha1_init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.initSha1
      (Spec.Hmac.sha1I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha1I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha1I.initAnyKeyApi) {
      code := initCode sha1Hash Spec.Hmac.sha1I 6
      verified := Sha1.initAny }
    576 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (hmacInitAnyOut Spec.Hmac.sha1I Proof.Hmac.sha1_local (by decide) _)
    (by dsimp only; lit_decide)

/-- `vg_hmac_sha1_finalize` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha1`) meets
its contract in constant time and returns without secret residue. -/
theorem sha1_finalize_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha1
      (Spec.Hmac.sha1I.finalizeContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha1I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha1I.finalizeApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha1I) .r7 sha1Hash.finalize
      verified := Sha1.finalize }
    576 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (hmacFinOut Spec.Hmac.sha1I (by decide) _)
    (by dsimp only; lit_decide)

/-- `vg_hmac_sha224_init` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.initSha224`) meets its
contract in constant time and returns without secret residue. -/
theorem sha224_init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.initSha224
      (Spec.Hmac.sha224I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha224I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha224I.initAnyKeyApi) {
      code := initCode sha224Hash Spec.Hmac.sha224I 6
      verified := Sha224.initAny }
    960 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (hmacInitAnyOut Spec.Hmac.sha224I Proof.Hmac.sha224_local (by decide) _)
    (by dsimp only; lit_decide)

/-- `vg_hmac_sha224_finalize` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha224`) meets
its contract in constant time and returns without secret residue. -/
theorem sha224_finalize_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha224
      (Spec.Hmac.sha224I.finalizeContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha224I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha224I.finalizeApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha224I) .r7 sha224Hash.finalize
      verified := Sha224.finalize }
    960 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (hmacFinOut Spec.Hmac.sha224I (by decide) _)
    (by dsimp only; lit_decide)

/-- `vg_hmac_sha256_init` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.initSha256`) meets its
contract in constant time and returns without secret residue. -/
theorem sha256_init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.initSha256
      (Spec.Hmac.sha256I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha256I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha256I.initAnyKeyApi) {
      code := initCode sha256Hash Spec.Hmac.sha256I 6
      verified := Sha256.initAny }
    960 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (hmacInitAnyOut Spec.Hmac.sha256I Proof.Hmac.sha256_local (by decide) _)
    (by dsimp only; lit_decide)

/-- `vg_hmac_sha256_finalize` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha256`) meets
its contract in constant time and returns without secret residue. -/
theorem sha256_finalize_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha256
      (Spec.Hmac.sha256I.finalizeContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha256I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha256I.finalizeApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha256I) .r7 sha256Hash.finalize
      verified := Sha256.finalize }
    960 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (hmacFinOut Spec.Hmac.sha256I (by decide) _)
    (by dsimp only; lit_decide)

/-- `vg_hmac_sha384_init` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.initSha384`) meets its
contract in constant time and returns without secret residue. -/
theorem sha384_init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.initSha384
      (Spec.Hmac.sha384I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha384I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha384I.initAnyKeyApi) {
      code := initCode sha384Hash Spec.Hmac.sha384I 7
      verified := Sha384.initAny }
    1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (hmacInitAnyOut Spec.Hmac.sha384I Proof.Hmac.sha384_local (by decide) _)
    (by dsimp only; lit_decide)

/-- `vg_hmac_sha384_finalize` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha384`) meets
its contract in constant time and returns without secret residue. -/
theorem sha384_finalize_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha384
      (Spec.Hmac.sha384I.finalizeContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha384I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha384I.finalizeApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha384I) .r7 sha384Hash.finalize
      verified := Sha384.finalize }
    1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (hmacFinOut Spec.Hmac.sha384I (by decide) _)
    (by dsimp only; lit_decide)

/-- `vg_hmac_sha512_init` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.initSha512`) meets its
contract in constant time and returns without secret residue. -/
theorem sha512_init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.initSha512
      (Spec.Hmac.sha512I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha512I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha512I.initAnyKeyApi) {
      code := initCode sha512Hash Spec.Hmac.sha512I 7
      verified := Sha512.initAny }
    1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (hmacInitAnyOut Spec.Hmac.sha512I Proof.Hmac.sha512_local (by decide) _)
    (by dsimp only; lit_decide)

/-- `vg_hmac_sha512_finalize` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha512`) meets
its contract in constant time and returns without secret residue. -/
theorem sha512_finalize_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha512
      (Spec.Hmac.sha512I.finalizeContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha512I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha512I.finalizeApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha512I) .r7 sha512Hash.finalize
      verified := Sha512.finalize }
    1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (hmacFinOut Spec.Hmac.sha512I (by decide) _)
    (by dsimp only; lit_decide)

/-- `vg_hmac_sha512_224_init` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.initSha512_224`) meets its
contract in constant time and returns without secret residue. -/
theorem sha512_224_init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.initSha512_224
      (Spec.Hmac.sha512_224I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha512_224I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha512_224I.initAnyKeyApi) {
      code := initCode sha512_224Hash Spec.Hmac.sha512_224I 7
      verified := Sha512_224.initAny }
    1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (hmacInitAnyOut Spec.Hmac.sha512_224I Proof.Hmac.sha512_224_local (by decide) _)
    (by dsimp only; lit_decide)

/-- `vg_hmac_sha512_224_finalize` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha512_224`) meets
its contract in constant time and returns without secret residue. -/
theorem sha512_224_finalize_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha512_224
      (Spec.Hmac.sha512_224I.finalizeContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha512_224I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha512_224I.finalizeApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha512_224I) .r7 sha512_224Hash.finalize
      verified := Sha512_224.finalize }
    1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (hmacFinOut Spec.Hmac.sha512_224I (by decide) _)
    (by dsimp only; lit_decide)

/-- `vg_hmac_sha512_256_init` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.initSha512_256`) meets its
contract in constant time and returns without secret residue. -/
theorem sha512_256_init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.initSha512_256
      (Spec.Hmac.sha512_256I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha512_256I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha512_256I.initAnyKeyApi) {
      code := initCode sha512_256Hash Spec.Hmac.sha512_256I 7
      verified := Sha512_256.initAny }
    1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (hmacInitAnyOut Spec.Hmac.sha512_256I Proof.Hmac.sha512_256_local (by decide) _)
    (by dsimp only; lit_decide)

/-- `vg_hmac_sha512_256_finalize` as emitted (`Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha512_256`) meets
its contract in constant time and returns without secret residue. -/
theorem sha512_256_finalize_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Hmac.Stream.PPC64LE.Fn.finalizeSha512_256
      (Spec.Hmac.sha512_256I.finalizeContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha512_256I)) 0 :=
  verifiedScrubbed (api := Spec.Hmac.sha512_256I.finalizeApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha512_256I) .r7 sha512_256Hash.finalize
      verified := Sha512_256.finalize }
    1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (hmacFinOut Spec.Hmac.sha512_256I (by decide) _)
    (by dsimp only; lit_decide)

end VG.Proof.Hmac.Stream.PPC64LE.Scrub
