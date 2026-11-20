module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Md5
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Sha256
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Sha384
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Sha512
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Sha512_224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Sha512_256
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Lit

/-!
# PBKDF2 on PPC64LE, without secret residue

Each hash's PBKDF2 as emitted (`Impl/Hmac/Stream/PPC64LE/Fn.lean`), followed
by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`, `PPC64LE.Scrub.verifiedScrubbedAll`),
which clears the volatile registers and the stack its frames used: `pbkdf2` keeps its working space in a frame it does
not wipe itself (`withStackScratch`), and calls HMAC's `init` and
`finalize`, PBKDF2's `iterate` and the hash's functions, which push frames
of their own. Its postcondition reads the memory on return only within
`out`, as on RISC-V (`Proof/Pbkdf2/Whole/RISCV64/Scrub.lean`).

What the cleanup needs of the code (`scrubSide`) is proved for each, by the
kernel's evaluation of it (`lit_decide`) when this module is built.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub
open VG.Impl.Hmac.Stream.PPC64LE (hmacFrame)
open VG.Impl.Pbkdf2.Whole.PPC64LE (md5F sha1F sha224F sha256F sha384F sha512F sha512_224F sha512_256F
  pbkFrame)

/-- PBKDF2's postcondition reads the memory on return only within `out`, the
derived key's bytes. -/
theorem pbkdf2Out (I : Spec.Hmac.Instance) (stack : Nat) :
    PostOut (I.pbkdf2Contract abi stack) (Spec.Pbkdf2.pbkdf2Sig.retBits 64) := by
  unfold Spec.Hmac.Instance.pbkdf2Contract Spec.Pbkdf2.pbkdf2Contract
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨pw, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 6) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pwLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨salt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨saltLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨c, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Pbkdf2.pbkdf2Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have ho : ∀ i < outLen.toNat, m₂ (out + BitVec.ofNat 64 i) = m₁ (out + BitVec.ofNat 64 i) :=
      fun i hi => (hb.2.2 _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))).symm
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 64] (Spec.Pbkdf2.pbkdf2Post I.S 64) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 64] (Spec.Pbkdf2.pbkdf2Post I.S 64) _ m m₂ r
    dsimp only [Curry.apply, Spec.Pbkdf2.pbkdf2Post, ArgWord.ofRaw] at h ⊢
    rw [Sha256.Stream.bytesAt_congr fun i hi => ho i (by
      rw [BitVec.toNat_setWidth] at hi; have := Nat.mod_le outLen.toNat (2 ^ 64); omega_using [hi])]
    exact h

/-- `vg_pbkdf2_hmac_md5` as emitted (`Impl.Pbkdf2.Whole.PPC64LE.Fn.md5`) meets its
contract in constant time and returns without secret residue. -/
theorem md5_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Pbkdf2.Whole.PPC64LE.Fn.md5
      (Spec.Hmac.md5I.pbkdf2Contract PPC64LE.abi
        (hmacFrame Spec.Hmac.md5I + 144 + pbkFrame Spec.Hmac.md5I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.md5I.pbkdf2Api) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (pbkFrame Spec.Hmac.md5I) .r10 md5F.pbkdf2
      verified := Proof.Pbkdf2.Whole.PPC64LE.Md5.pbkdf2 }
    1616 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (pbkdf2Out Spec.Hmac.md5I _)
    (by dsimp only; lit_decide)

/-- `vg_pbkdf2_hmac_sha1` as emitted (`Impl.Pbkdf2.Whole.PPC64LE.Fn.sha1`) meets its
contract in constant time and returns without secret residue. -/
theorem sha1_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Pbkdf2.Whole.PPC64LE.Fn.sha1
      (Spec.Hmac.sha1I.pbkdf2Contract PPC64LE.abi
        (hmacFrame Spec.Hmac.sha1I + 144 + pbkFrame Spec.Hmac.sha1I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha1I.pbkdf2Api) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (pbkFrame Spec.Hmac.sha1I) .r10 sha1F.pbkdf2
      verified := Proof.Pbkdf2.Whole.PPC64LE.Sha1.pbkdf2 }
    1776 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (pbkdf2Out Spec.Hmac.sha1I _)
    (by dsimp only; lit_decide)

/-- `vg_pbkdf2_hmac_sha224` as emitted (`Impl.Pbkdf2.Whole.PPC64LE.Fn.sha224`) meets its
contract in constant time and returns without secret residue. -/
theorem sha224_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Pbkdf2.Whole.PPC64LE.Fn.sha224
      (Spec.Hmac.sha224I.pbkdf2Contract PPC64LE.abi
        (hmacFrame Spec.Hmac.sha224I + 144 + pbkFrame Spec.Hmac.sha224I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha224I.pbkdf2Api) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (pbkFrame Spec.Hmac.sha224I) .r10 sha224F.pbkdf2
      verified := Proof.Pbkdf2.Whole.PPC64LE.Sha224.pbkdf2 }
    2640 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (pbkdf2Out Spec.Hmac.sha224I _)
    (by dsimp only; lit_decide)

/-- `vg_pbkdf2_hmac_sha256` as emitted (`Impl.Pbkdf2.Whole.PPC64LE.Fn.sha256`) meets its
contract in constant time and returns without secret residue. -/
theorem sha256_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Pbkdf2.Whole.PPC64LE.Fn.sha256
      (Spec.Hmac.sha256I.pbkdf2Contract PPC64LE.abi
        (hmacFrame Spec.Hmac.sha256I + 144 + pbkFrame Spec.Hmac.sha256I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha256I.pbkdf2Api) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (pbkFrame Spec.Hmac.sha256I) .r10 sha256F.pbkdf2
      verified := Proof.Pbkdf2.Whole.PPC64LE.Sha256.pbkdf2 }
    2640 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (pbkdf2Out Spec.Hmac.sha256I _)
    (by dsimp only; lit_decide)

/-- `vg_pbkdf2_hmac_sha384` as emitted (`Impl.Pbkdf2.Whole.PPC64LE.Fn.sha384`) meets its
contract in constant time and returns without secret residue. -/
theorem sha384_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Pbkdf2.Whole.PPC64LE.Fn.sha384
      (Spec.Hmac.sha384I.pbkdf2Contract PPC64LE.abi
        (hmacFrame Spec.Hmac.sha384I + 144 + pbkFrame Spec.Hmac.sha384I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha384I.pbkdf2Api) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (pbkFrame Spec.Hmac.sha384I) .r10 sha384F.pbkdf2
      verified := Proof.Pbkdf2.Whole.PPC64LE.Sha384.pbkdf2 }
    5440 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (pbkdf2Out Spec.Hmac.sha384I _)
    (by dsimp only; lit_decide)

/-- `vg_pbkdf2_hmac_sha512` as emitted (`Impl.Pbkdf2.Whole.PPC64LE.Fn.sha512`) meets its
contract in constant time and returns without secret residue. -/
theorem sha512_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Pbkdf2.Whole.PPC64LE.Fn.sha512
      (Spec.Hmac.sha512I.pbkdf2Contract PPC64LE.abi
        (hmacFrame Spec.Hmac.sha512I + 144 + pbkFrame Spec.Hmac.sha512I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512I.pbkdf2Api) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (pbkFrame Spec.Hmac.sha512I) .r10 sha512F.pbkdf2
      verified := Proof.Pbkdf2.Whole.PPC64LE.Sha512.pbkdf2 }
    5440 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (pbkdf2Out Spec.Hmac.sha512I _)
    (by dsimp only; lit_decide)

/-- `vg_pbkdf2_hmac_sha512_224` as emitted (`Impl.Pbkdf2.Whole.PPC64LE.Fn.sha512_224`) meets its
contract in constant time and returns without secret residue. -/
theorem sha512_224_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Pbkdf2.Whole.PPC64LE.Fn.sha512_224
      (Spec.Hmac.sha512_224I.pbkdf2Contract PPC64LE.abi
        (hmacFrame Spec.Hmac.sha512_224I + 144 + pbkFrame Spec.Hmac.sha512_224I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512_224I.pbkdf2Api) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (pbkFrame Spec.Hmac.sha512_224I) .r10 sha512_224F.pbkdf2
      verified := Proof.Pbkdf2.Whole.PPC64LE.Sha512_224.pbkdf2 }
    5440 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (pbkdf2Out Spec.Hmac.sha512_224I _)
    (by dsimp only; lit_decide)

/-- `vg_pbkdf2_hmac_sha512_256` as emitted (`Impl.Pbkdf2.Whole.PPC64LE.Fn.sha512_256`) meets its
contract in constant time and returns without secret residue. -/
theorem sha512_256_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Pbkdf2.Whole.PPC64LE.Fn.sha512_256
      (Spec.Hmac.sha512_256I.pbkdf2Contract PPC64LE.abi
        (hmacFrame Spec.Hmac.sha512_256I + 144 + pbkFrame Spec.Hmac.sha512_256I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512_256I.pbkdf2Api) {
      code := Impl.StackScratch.PPC64LE.withStackScratch (pbkFrame Spec.Hmac.sha512_256I) .r10 sha512_256F.pbkdf2
      verified := Proof.Pbkdf2.Whole.PPC64LE.Sha512_256.pbkdf2 }
    5440 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (pbkdf2Out Spec.Hmac.sha512_256I _)
    (by dsimp only; lit_decide)

end VG.Proof.Pbkdf2.Whole.PPC64LE.Scrub
