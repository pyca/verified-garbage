module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Md5
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
public import VerifiedGarbage.Spec.HashId

/-!
# Tiers of Merkle–Damgård hash functions on x86-64

A function that takes the hash function as an argument (by its number,
`Spec/HashId.lean`) calls the one its argument names through a dispatch
(`Impl/Dispatch.lean`), so each of its instances calls one implementation of
each hash function: a `Tier`, a variant of the interface `MdHashTier` on
x86-64 (`Variants/MdHashTier/X86_64/`). Its hash functions are those of
`HashId` from 0 to 7 (MD5 to SHA-512/256), in that order (`mgf_ok`,
`hmac_ok`), made with one implementation of each compression function:
SHA-1's, SHA-256's (for SHA-224 and SHA-256) and SHA-512's (for SHA-384,
SHA-512, SHA-512/224 and SHA-512/256) (`Tier.of`). An instance needs the
CPU features of all of them, and its name ends with the tier's suffix,
qualified by its interface's tag (`Emit.qualifiedName`), e.g.
`vg_rsa_oaep_decrypt_hash_shani_avx2`.

Each tier is the fastest implementation of each compression function on a
kind of CPU, as `src/hashes/` chooses them: so its suffix names the CPU
features that choose them, not each implementation.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64

/-- A tier: an implementation of each hash function, by its number. -/
structure Tier where
  /-- What the names of its instances end with (e.g. `_shani_avx2`; nothing
  for the baseline implementations). -/
  suffix : String
  /-- MD5, SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and
  SHA-512/256: the hash function `i` names is the `i`th. -/
  hashes : List MdHash
  /-- They are those `HashId.mgf1` numbers, as RSA's padding takes them. -/
  mgf_ok : hashes.map (some ·.mgf.G) = (List.range 8).map Spec.HashId.mgf1
  /-- They are those `HashId.hmac` numbers, as HMAC takes them. -/
  hmac_ok : hashes.map (some ·.I.S.H) = (List.range 8).map Spec.HashId.hmac
  /-- The CPU features of their implementations, each once. -/
  features : List String

/-- The tier of an implementation of SHA-1's (`c1`), SHA-256's (`c256`) and
SHA-512's (`c512`) compression functions. -/
def Tier.of (suffix : String) (c1 : Proof.Sha1.X86_64.Compress) (c256 : Proof.Sha256.X86_64.Compress)
    (c512 : Proof.Sha512.X86_64.Compress) : Tier where
  suffix := suffix
  hashes := [Md5.variant, Sha1.variant c1, Sha224.variant c256, Sha256.variant c256, Sha512.sha384 c512,
    Sha512.sha512 c512, Sha512.sha512_224 c512, Sha512.sha512_256 c512]
  mgf_ok := rfl
  hmac_ok := rfl
  features := (c1.features ++ c256.features ++ c512.features).eraseDups

/-- The hash function `i` names in the tier `t`. -/
def Tier.get (t : Tier) (i : Nat) : Option MdHash := t.hashes[i]?

end VG.Proof.Pbkdf2.Md.X86_64
