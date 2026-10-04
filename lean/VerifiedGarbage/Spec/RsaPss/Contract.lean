import VerifiedGarbage.Spec.RsaPss
import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSASSA-PSS: the contracts, on every target

**Trusted** (as every file in `Spec/`). For the hash function `H` and MGF1
with the hash function `G` (any two of `Mgf1.hashes`), in the module
`rsa_pss_<H>_mgf1_<G>`:

* `vg_rsa_pss_<H>_mgf1_<G>_verify`: `RSASSA-PSS-VERIFY` of a signature for a
  digest (`RsaPss.verify`), expecting a salt length or any.

Numbers are as in `Spec/Rsa/Contract.lean`: slices of octets, most
significant first, with the modulus `n` of `n_len` octets, from 64 to 1024,
and `e` of at most `n_len`. The digest is `hLen` octets, an array. These are
preconditions, on the public lengths; everything about the values is
checked, and the function returns 1 for a valid signature and 0 otherwise.

The signature determines memory validity, separation and that the pointers,
the lengths and the salt length arguments are public, through
`Sig.contract`. The public key, `n` and `e`, is public too, and may affect
timing (`leak`). Nothing else is: the digest, the signature, and everything
verification computes from them (`EM`, `DB`, where its padding ends, the
salt and its length, whether each check passes) are secret, and only the
returned bit tells whether the signature is valid.

`scratch` is working space of at least `scratchWords n_len` `u64`s (that of
the RSA primitives, and room for the encoding, the hash functions' states
and their working space), whose contents on return are unspecified.
`stack` is the number of bytes below the stack pointer that an
implementation's calls and frames use. The functions may overwrite their
arguments passed in memory, where the calling convention allows it
(`writeArgs`).
-/

namespace VG.Spec.RsaPss

open Mgf1 (Hash)
open Rsa (bytesAt lenValid)

/-- The least working space, in `u64`s, for a modulus of `nLen` octets: the
RSA primitives' (`Rsa.scratchWords`), and 1024 more. -/
def scratchWords (nLen : Nat) : Nat := Rsa.scratchWords nLen + 1024

/-- The `# Safety` items on the working space. -/
def scratchSafety : List String :=
  ["`scratch_len` must be at least `16 * n_len + 1024`.",
    "The contents of `scratch` on return are unspecified and may contain secrets; the caller \
      must destroy them after use."]

/-- The salt length verification expects, from the arguments `salt_len` and
`any_salt_len`: any if `any_salt_len` is not zero, otherwise `salt_len`. -/
def expectedSaltLen {w : Nat} (saltLen : BitVec w) (anySaltLen : BitVec 32) : Option Nat :=
  if anySaltLen = 0 then some saltLen.toNat else none

variable (H G : Hash)

/-! ## `vg_rsa_pss_<H>_mgf1_<G>_verify` -/

/-- `vg_rsa_pss_<H>_mgf1_<G>_verify(n: *const u8, n_len: usize, e: *const u8,
e_len: usize, digest: *const [u8; hLen], sig: *const u8, sig_len: usize,
salt_len: usize, any_salt_len: u32, scratch: *mut u64, scratch_len: usize)
-> u32`. -/
def verifySig : Sig where
  params := [("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("digest", .array false .u8 H.len), ("sig", .slice false .u8 "sig_len"),
    ("salt_len", .int .usize true), ("any_salt_len", .int .u32 true),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- `RSASSA-PSS-VERIFY` of the signature for the digest with the public key
`(n, e)`, expecting the salt length `expectedSaltLen salt_len any_salt_len`
(`verify`): returns 1 if it is valid and 0 otherwise. Constant time but for
the public key. -/
def verifyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (verifySig H).contract A
    (pre := fun _n nLen _e eLen _digest _sig sigLen _saltLen _anySaltLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        sigLen.toNat = nLen.toNat ∧ scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun n nLen e eLen digest sig _sigLen saltLen anySaltLen _scratch _scratchLen m _m'
        r =>
      r = if verify H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m digest H.len)
          (bytesAt m sig nLen.toNat) (expectedSaltLen saltLen anySaltLen) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun n nLen e eLen _digest _sig _sigLen _saltLen _anySaltLen _scratch
        _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

/-- `vg_rsa_pss_<H>_mgf1_<G>_verify` on every target. -/
def verifyApi : Api where
  module := s!"rsa_pss_{H.rust}_mgf1_{G.rust}"
  name := s!"vg_rsa_pss_{H.rust}_mgf1_{G.rust}_verify"
  sig := verifySig H
  writeArgs := true
  contracts := some fun A stack => verifyContract H G A stack
  summary := s!"RSASSA-PSS signature verification (RFC 8017 §8.1.2) with {H.name} and MGF1 \
    with {G.name}, of a signature of a {H.name} digest. With the modulus `n` (`n_len` bytes, \
    most significant first, odd, from 512 to 8192 bits, its first byte not zero) and the \
    public exponent `e` (`e_len` bytes, most significant first), returns 1 if `sig` (`n_len` \
    bytes, most significant first) is an RSASSA-PSS signature of the {H.len}-byte digest \
    `*digest` with a salt of `salt_len` bytes, or of any length if `any_salt_len` is not zero \
    (BoringSSL's `RSA_PSS_SALTLEN_AUTO`); and 0 if it is not, or if `n` is not such a \
    modulus or `sig` is not below it.\n\n\
    Contract: `VG.Spec.RsaPss.verifyContract` of `VG.Spec.Mgf1.{H.lean}` and \
    `VG.Spec.Mgf1.{G.lean}`. Constant time but for the public key: timing may depend on the \
    pointers, the lengths, `salt_len`, `any_salt_len` and the contents of `n` and `e`, not on \
    the digest, the signature or anything computed from them but the result."
  safety := ["`n_len` must be in 64..=1024.", "`sig_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`."] ++ scratchSafety

end VG.Spec.RsaPss
