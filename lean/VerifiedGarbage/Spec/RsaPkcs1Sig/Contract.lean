module

public import VerifiedGarbage.Spec.RsaPkcs1Sig
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSASSA-PKCS1-v1_5: the contracts, on every target

**Trusted** (as every file in `Spec/`). In the module `rsa_pkcs1_sig`:

* `vg_rsa_pkcs1_sign`: RSASSA-PKCS1-V1_5-SIGN of a hash value
  (`RsaPkcs1Sig.sign`), with the private key in the CRT form that
  `vg_rsa_private_checked` takes;
* `vg_rsa_pkcs1_verify`: RSASSA-PKCS1-V1_5-VERIFY of a hash value
  (`RsaPkcs1Sig.verify`);
* `vg_rsa_pkcs1_recover`: the hash value a signature signs
  (`RsaPkcs1Sig.recover`).

The numbers are as in `Spec/Rsa/Contract.lean`: slices of octets, most
significant first, the modulus `n` `n_len` octets, from 64 to 1024, and `e`
at most `n_len` octets. The hash function is a public `u32`, `hash`, its
number in `Hash.ofId` (0 for MD5 to 11 for SHA3-512); any other number
names none, and the function fails. The signature and the hash value may be
of any length; the functions check it.

Signing is constant time but for the public key (`leak`), the hash
function and the lengths: the hash value, the private key and the signature
are secret. It returns 1 and writes the signature, 0 and zeros if the key
or the hash value is refused, or 2 and zeros on the internal error of
`vg_rsa_private_checked` (the signature fails its check against `e`).

Everything about a verification is public: the public key, the hash value
and the signature, and so whether the signature is valid, may all affect
timing (`leak`), as in BoringSSL ("This is part of signature verification
and thus does not need to run in constant-time", `padding.cc.inc`).

`scratch` is working space of at least `16 n_len` `u64`s, whose contents on
return are unspecified, and `stack` the number of bytes below the stack
pointer that an implementation's calls and frames use, as for the RSA
primitives. The functions may overwrite their arguments passed in memory,
where the calling convention allows it (`writeArgs`).
-/

@[expose] public section

namespace VG.Spec.RsaPkcs1Sig

open Rsa

/-! ## `vg_rsa_pkcs1_sign` -/

/-- `vg_rsa_pkcs1_sign(out: *mut u8, out_len: usize, n: *const u8,
n_len: usize, e: *const u8, e_len: usize, hash: u32, digest: *const u8,
digest_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize,
dp: *const u8, dp_len: usize, dq: *const u8, dq_len: usize,
qinv: *const u8, qinv_len: usize, scratch: *mut u64, scratch_len: usize)
-> u32`. -/
def signSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("hash", .int .u32 true),
    ("digest", .slice false .u8 "digest_len"), ("p", .slice false .u8 "p_len"),
    ("q", .slice false .u8 "q_len"), ("dp", .slice false .u8 "dp_len"),
    ("dq", .slice false .u8 "dq_len"), ("qinv", .slice false .u8 "qinv_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- The signature of the hash value `digest` with the hash function numbered
`hash` (`sign`): `invalid` if `hash` names no hash function. -/
def signId (nB eB pB qB dPB dQB qInvB : List Byte) (hash : Nat) (digest : List Byte) :
    Outcome :=
  match Hash.ofId hash with
  | some h => sign nB eB pB qB dPB dQB qInvB h digest
  | none => .invalid

/-- RSASSA-PKCS1-V1_5-SIGN (`sign`), with the result as
`vg_rsa_private_checked` gives it (`writtenOutcome`). Constant time but for
the public key. -/
def signContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  signSig.contract A
    (pre := fun _out outLen _n nLen _e eLen _hash _digest _digestLen _p pLen _q qLen _dp dpLen
        _dq dqLen _qinv qinvLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen n nLen e eLen hash digest digestLen p pLen q qLen dp _dpLen dq
        _dqLen qinv _qinvLen _scratch _scratchLen m m' r =>
      writtenOutcome m' out nLen.toNat r
        (signId (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m p pLen.toNat)
          (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat) (bytesAt m dq qLen.toNat)
          (bytesAt m qinv pLen.toNat) hash.toNat (bytesAt m digest digestLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _hash _digest _digestLen _p _pLen _q _qLen _dp
        _dpLen _dq _dqLen _qinv _qinvLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

/-! ## `vg_rsa_pkcs1_verify` -/

/-- `vg_rsa_pkcs1_verify(n: *const u8, n_len: usize, e: *const u8,
e_len: usize, hash: u32, digest: *const u8, digest_len: usize,
sig: *const u8, sig_len: usize, scratch: *mut u64, scratch_len: usize)
-> u32`. -/
def verifySig : Sig where
  params := [("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("hash", .int .u32 true), ("digest", .slice false .u8 "digest_len"),
    ("sig", .slice false .u8 "sig_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- Whether `sig` is a valid signature of the hash value `digest` with the
hash function numbered `hash` and the public key `(n, e)`: false if `hash`
names no hash function. -/
def verifyId (nB eB : List Byte) (hash : Nat) (digest sig : List Byte) : Bool :=
  match Hash.ofId hash with
  | some h => verify nB eB h digest sig
  | none => false

/-- RSASSA-PKCS1-V1_5-VERIFY (`verify`): returns 1 if the signature is
valid, 0 if not. Not constant time: everything it reads is public. -/
def verifyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  verifySig.contract A
    (pre := fun _n nLen _e eLen _hash _digest _digestLen _sig _sigLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun n nLen e eLen hash digest digestLen sig sigLen _scratch _scratchLen m _m' r =>
      r = if verifyId (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) hash.toNat
          (bytesAt m digest digestLen.toNat) (bytesAt m sig sigLen.toNat) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun n nLen e eLen _hash digest digestLen sig sigLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat ++ bytesAt m digest digestLen.toNat ++
        bytesAt m sig sigLen.toNat).map (·.toNat))

/-- The documentation's list of the hash functions' numbers. -/
def hashIdsDoc : String :=
  "`hash` names the hash function: 0 MD5, 1 SHA-1, 2 SHA-224, 3 SHA-256, 4 SHA-384, \
    5 SHA-512, 6 SHA-512/224, 7 SHA-512/256, 8 SHA3-224, 9 SHA3-256, 10 SHA3-384, \
    11 SHA3-512 (`VG.Spec.RsaPkcs1Sig.Hash.ofId`)"

def signApi : Api where
  module := "rsa_pkcs1_sig"
  name := "vg_rsa_pkcs1_sign"
  sig := signSig
  writeArgs := true
  contracts := some fun A stack => signContract A stack
  summary := s!"RSASSA-PKCS1-v1_5 signature generation (RFC 8017 §8.2.1) of a hash value, \
    as BoringSSL's `RSA_sign` does it. With the modulus `n` (`n_len` bytes, most \
    significant first, odd, from 512 to 8192 bits, its first byte not zero), \
    {Rsa.exponentDoc} and the private key `(p, q, dP, dQ, qInv)` (as \
    `vg_rsa_private_checked` takes it), encodes `digest` with EMSA-PKCS1-v1_5 (RFC 8017 \
    §9.2: `0x00 0x01`, bytes `0xff`, `0x00` and the DER encoding of its `DigestInfo`) to \
    `n_len` bytes and computes the signature from it as `vg_rsa_private_checked` does: \
    writes it to `out` (`n_len` bytes, most significant first) and returns 1; writes zeros \
    and returns 0 if `hash` names no hash function, `digest` is not as long as its values, \
    `n_len` is less than the encoding's 11 bytes more than the `DigestInfo`, or \
    `vg_rsa_private_checked` refuses the key; and writes zeros and returns 2 (an internal \
    error) if the signature fails the check against `e`, which is the case for no hash \
    value if `vg_rsa_check_key` accepts the key and `p` and `q` are prime. A signature it \
    writes is one `vg_rsa_pkcs1_verify` accepts. {hashIdsDoc}.\n\n\
    Contract: `VG.Spec.RsaPkcs1Sig.signContract`. Constant time but for the public key: \
    timing may depend on the pointers, the lengths, `hash` and the contents of `n` and \
    `e`, not on `digest` or the private key."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`.", "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`."] ++ scratchSafety

def verifyApi : Api where
  module := "rsa_pkcs1_sig"
  name := "vg_rsa_pkcs1_verify"
  sig := verifySig
  writeArgs := true
  contracts := some fun A stack => verifyContract A stack
  summary := s!"RSASSA-PKCS1-v1_5 signature verification (RFC 8017 §8.2.2) of a hash value, \
    as BoringSSL's `RSA_verify` does it. With the modulus `n` (`n_len` bytes, most \
    significant first, odd, from 512 to 8192 bits, its first byte not zero) and \
    {Rsa.exponentDoc}, returns 1 if `sig` is `n_len` \
    bytes, the integer `s` of `sig` (most significant byte first) is below `n`, and \
    `s^e mod n` (as `n_len` bytes) is `0x00 0x01`, at least 8 bytes `0xff`, `0x00` and then \
    exactly the DER encoding of the `DigestInfo` of `digest` (RFC 8017 §9.2 note 1), which \
    must be as long as the hash function's values; and 0 otherwise, or if `n` or `e` is not \
    such a number or `hash` names no hash function. That is, exactly when `s^e mod n` is \
    EMSA-PKCS1-v1_5's encoding of `digest`: the signed `DigestInfo` is compared, never \
    parsed. {hashIdsDoc}.\n\n\
    Contract: `VG.Spec.RsaPkcs1Sig.verifyContract`. Not constant time: timing may depend \
    on the pointers, the lengths, `hash` and the contents of `n`, `e`, `digest` and `sig`."
  safety := ["`n_len` must be in 64..=1024.", "`e_len` must be in 1..=`n_len`."] ++ scratchSafety

/-! ## `vg_rsa_pkcs1_recover` -/

/-- `vg_rsa_pkcs1_recover(out: *mut u8, out_len: usize, n: *const u8,
n_len: usize, e: *const u8, e_len: usize, hash: u32, sig: *const u8,
sig_len: usize, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def recoverSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("hash", .int .u32 true),
    ("sig", .slice false .u8 "sig_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- The hash value the signature signs (`recover`), for the hash function
numbered `hash`, which must name one, and whose values `out` is as long as.
Not constant time: everything it reads is public. -/
def recoverContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  recoverSig.contract A
    (pre := fun _out outLen _n nLen _e eLen hash _sig _sigLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        (∃ h, Hash.ofId hash.toNat = some h ∧ outLen.toNat = h.len) ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out outLen n nLen e eLen hash sig sigLen _scratch _scratchLen m m' r =>
      ∀ h, Hash.ofId hash.toNat = some h →
        written m' out outLen.toNat r
          (recover (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) h (bytesAt m sig sigLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _hash sig sigLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat ++ bytesAt m sig sigLen.toNat).map
        (·.toNat))

def recoverApi : Api where
  module := "rsa_pkcs1_sig"
  name := "vg_rsa_pkcs1_recover"
  sig := recoverSig
  writeArgs := true
  contracts := some fun A stack => recoverContract A stack
  summary := s!"The hash value an RSASSA-PKCS1-v1_5 signature signs, as BoringSSL's \
    `EVP_PKEY_verify_recover` returns it for an RSA key with PKCS #1 v1.5 padding and a \
    hash function set. With the modulus `n` (`n_len` bytes, most significant first, odd, \
    from 512 to 8192 bits, its first byte not zero) and {Rsa.exponentDoc}, if `sig` is \
    `n_len` bytes, the integer `s` of `sig` \
    (most significant byte first) is below `n`, and `s^e mod n` (as `n_len` bytes) is \
    `0x00 0x01`, at least 8 bytes `0xff`, `0x00` and then the DER encoding of the hash \
    function's `DigestInfo` prefix (RFC 8017 §9.2 note 1) followed by exactly `out_len` \
    bytes, writes those bytes to `out` and returns 1; otherwise, or if `n` or `e` is not \
    such a number, writes zeros and returns 0. It writes a value exactly when \
    `vg_rsa_pkcs1_verify` accepts the signature for it. {hashIdsDoc}.\n\n\
    Contract: `VG.Spec.RsaPkcs1Sig.recoverContract`. Not constant time: timing may depend \
    on the pointers, the lengths, `hash` and the contents of `n`, `e` and `sig`."
  safety := ["`n_len` must be in 64..=1024.", "`e_len` must be in 1..=`n_len`.",
    "`hash` must be in 0..=11, and `out_len` the length of its hash function's values."] ++
    scratchSafety

end VG.Spec.RsaPkcs1Sig
