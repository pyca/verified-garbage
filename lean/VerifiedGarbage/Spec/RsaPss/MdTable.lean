module

public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.Spec.RsaPss.Contract
public import VerifiedGarbage.Spec.MdHashTable
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute

/-!
# RSASSA-PSS with both of its hash functions given as tables of `MdHash`

**Trusted** (as every file in `Spec/`). In the module `rsa_pss`, each with
two last parameters, tables of the interface `MdHash`
(`Spec/MdHashTable.lean`): `hash`, naming the hash function `H` of the
digest and of EMSA-PSS, and `mgf1`, naming MGF1's `G`
(`MdHashTable.hashAt`):

* `vg_rsa_pss_sign`: `RSASSA-PSS-SIGN` of a digest with a salt, with the
  private key checked against the public exponent (`RsaPss.sign H G`);
* `vg_rsa_pss_sign_precomputed`: `vg_rsa_pss_sign` given the key's
  precomputed values (`Rsa.privatePrecompute`, `Spec/Rsa/PrivatePrecompute.lean`);
* `vg_rsa_pss_verify_precomputed`: `RSASSA-PSS-VERIFY` of a signature for a
  digest (`RsaPss.verify H G`), expecting a salt length or any, given the
  modulus' `Rsa.publicPrecompute` values `pre`.

So one function serves every pair of hash functions, with every
implementation of each, rather than a function for each pair. `H` is a
table of its compression function because verification hashes
`M' = 0⁸ ‖ mHash ‖ salt`, whose length is secret when any salt length is
accepted: it pads `M'` itself and compresses a public number of blocks.

Numbers are as in `Spec/Rsa/Contract.lean`: slices of octets, most
significant first, with the modulus `n` of `n_len` octets, from 64 to 1024,
and `e` of at most `n_len`; the private key is as `vg_rsa_private_checked`
takes it. The digest is a slice of `digest_len` octets, which must be `H`'s
length. These are preconditions, on the public lengths; everything about
the values is checked. Signing returns 1 and writes the signature, or
writes zeros and returns 0 (the encoding or the key refused) or 2 (the
internal error: the result failed its check against `e`); verification
returns 1 for a valid signature and 0 otherwise. With a `pre` that does
not hold the values for `n`, what verification returns is unspecified, as
in `Proof.Rsa.publicPrecomputedCheckedContract`.

The signature determines memory validity, separation and that the pointers,
the lengths and the salt length arguments are public, through
`Sig.contract` (among them the salt's length when signing); which tables
`hash` and `mgf1` are, is public too (`Abi.withTables`), and the tables'
own memory is read-only. The public key, `n` and `e`, and `pre` are
public, and may affect timing (`leak`). Nothing else is: when signing, the
private key, the digest, the salt and everything computed from them; when
verifying, the digest, the signature, and everything verification computes
from them (`EM`, `DB`, where its padding ends, the salt and its length,
whether each check passes) are secret, and only the returned bit tells
whether the signature is valid.

`scratch` is working space of at least `scratchWords n_len` `u64`s when
signing and `publicScratchWords n_len` when verifying (that of the RSA
primitive, and room for the encoding, the hash functions' states and their
working space), whose contents on return are unspecified.
`stack` is the number of bytes below the stack pointer that an
implementation's calls and frames use. The functions may overwrite their
arguments passed in memory, where the calling convention allows it
(`writeArgs`).
-/

@[expose] public section

namespace VG.Spec.RsaPss

open Mgf1 (Hash)
open Rsa (bytesAt lenValid writtenOutcome exponentDoc)

/-- The `# Safety` item of `hash`, but for what the emitter adds (which
tables it may be, `Rust.fnTablesDoc`). -/
def hashSafety : String :=
  "`hash` names the hash function of the digest and of the encoding: the one of \
    `VG.Spec.Mgf1.hashes` at the index in its first word of data (the hash functions' \
    `MdHash` tables of this crate, `fn_tables`, say which they name)."

/-- The `# Safety` item of `mgf1`, but for what the emitter adds. -/
def mgf1Safety : String :=
  "`mgf1` names MGF1's hash function: the one of `VG.Spec.Mgf1.hashes` at the index in its \
    first word of data (the hash functions' tables of this crate, `fn_tables`, say which they \
    name)."

/-- The `# Safety` item of `digest_len`. -/
def digestLenSafety : String :=
  "`digest_len` must be the digest length of the hash function `hash` names."

/-- The digest's length is that of the hash function the table at `hash`
names, if it names one. -/
def digestLenOk {w : Nat} (ptrBits : Nat) (m : Mem) (hash : Addr) (digestLen : BitVec w) :
    Prop :=
  ∀ H, MdHashTable.hashAt ptrBits m hash = some H → digestLen.toNat = H.len

/-! ## `vg_rsa_pss_sign` -/

/-- The parameters of signing: `(out: *mut u8, out_len: usize, n: *const u8,
n_len: usize, e: *const u8, e_len: usize, p: *const u8, p_len: usize,
q: *const u8, q_len: usize, dp: *const u8, dp_len: usize, dq: *const u8,
dq_len: usize, qinv: *const u8, qinv_len: usize, digest: *const u8,
digest_len: usize, salt: *const u8, salt_len: usize, scratch: *mut u64,
scratch_len: usize, hash: *const [usize; 11], mgf1: *const [usize; 11])
-> u32`, with `hash` and `mgf1` tables of `MdHash`. -/
def signMdTableSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("p", .slice false .u8 "p_len"),
    ("q", .slice false .u8 "q_len"), ("dp", .slice false .u8 "dp_len"),
    ("dq", .slice false .u8 "dq_len"), ("qinv", .slice false .u8 "qinv_len"),
    ("digest", .slice false .u8 "digest_len"), ("salt", .slice false .u8 "salt_len"),
    ("scratch", .slice true .u64 "scratch_len"), ("hash", MdHashTable.param),
    ("mgf1", MdHashTable.param)]
  ret := some .u32

/-- `RSASSA-PSS-SIGN` of the digest with the salt, with the private key
`(p, q, dP, dQ, qInv)` of the modulus `n` checked against the public exponent
`e` (`sign H G`), for `H` and `G` the hash functions `hash` and `mgf1` name.
Constant time but for the public key. -/
def signMdTableContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  signMdTableSig.contract A
    (pre := fun _out outLen _n nLen _e eLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv qinvLen
        _digest digestLen _salt _saltLen _scratch scratchLen hash _mgf1 m =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat ∧ digestLenOk A.ptrBits m hash digestLen)
    (post := fun out _outLen n nLen e eLen p pLen q qLen dp _dpLen dq _dqLen qinv _qinvLen
        digest _digestLen salt saltLen _scratch _scratchLen hash mgf1 m m' r =>
      ∀ H G, MdHashTable.hashAt A.ptrBits m hash = some H →
        MdHashTable.hashAt A.ptrBits m mgf1 = some G →
        writtenOutcome m' out nLen.toNat r
          (sign H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m p pLen.toNat)
            (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat) (bytesAt m dq qLen.toNat)
            (bytesAt m qinv pLen.toNat) (bytesAt m digest H.len)
            (bytesAt m salt saltLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _p _pLen _q _qLen _dp _dpLen _dq _dqLen _qinv
        _qinvLen _digest _digestLen _salt _saltLen _scratch _scratchLen _hash _mgf1 m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

/-! ## `vg_rsa_pss_verify_precomputed` -/

/-- The parameters of verification: `(n: *const u8, n_len: usize,
e: *const u8, e_len: usize, digest: *const u8, digest_len: usize,
sig: *const u8, sig_len: usize, salt_len: usize, any_salt_len: u32,
scratch: *mut u64, scratch_len: usize, pre: *const u64, pre_len: usize,
hash: *const [usize; 11], mgf1: *const [usize; 11]) -> u32`, with `pre` the
modulus' precomputed `u64` words, `hash` and `mgf1` tables
of `MdHash`. -/
def verifyPrecomputedMdTableSig : Sig where
  params := [("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("digest", .slice false .u8 "digest_len"), ("sig", .slice false .u8 "sig_len"),
    ("salt_len", .int .usize true), ("any_salt_len", .int .u32 true),
    ("scratch", .slice true .u64 "scratch_len"), ("pre", .slice false .u64 "pre_len"),
    ("hash", MdHashTable.param), ("mgf1", MdHashTable.param)]
  ret := some .u32

/-- `RSASSA-PSS-VERIFY` of the signature for the digest with the public key
`(n, e)`, expecting the salt length `expectedSaltLen salt_len any_salt_len`
(`verify H G`), for `H` and `G` the hash functions `hash` and `mgf1` name,
given precomputed values `pre` for the modulus: returns 1 if it is valid and
0 otherwise, if `pre` holds `Rsa.publicPrecompute n`. Constant time but for
the public key and `pre`. -/
def verifyPrecomputedMdTableContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  verifyPrecomputedMdTableSig.contract A
    (pre := fun _n nLen _e eLen _digest digestLen _sig sigLen _saltLen _anySaltLen _scratch
        scratchLen _pre preLen hash _mgf1 m =>
      lenValid nLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        sigLen.toNat = nLen.toNat ∧ publicScratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.precomputedWords nLen.toNat ∧ digestLenOk A.ptrBits m hash digestLen)
    (post := fun n nLen e eLen digest _digestLen sig _sigLen saltLen anySaltLen _scratch
        _scratchLen pre preLen hash mgf1 m _m' r =>
      ∀ H G, MdHashTable.hashAt A.ptrBits m hash = some H →
        MdHashTable.hashAt A.ptrBits m mgf1 = some G →
        Rsa.publicPrecompute (bytesAt m n nLen.toNat) = some (Rsa.wordsAt m pre preLen.toNat) →
          r = if verify H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
              (bytesAt m digest H.len) (bytesAt m sig nLen.toNat)
              (expectedSaltLen saltLen anySaltLen) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun n nLen e eLen _digest _digestLen _sig _sigLen _saltLen _anySaltLen
        _scratch _scratchLen pre preLen _hash _mgf1 m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        (Rsa.wordsAt m pre preLen.toNat).map (·.toNat))

/-- `vg_rsa_pss_verify_precomputed` on every target. -/
def verifyPrecomputedMdTableApi : Api where
  module := "rsa_pss"
  name := "vg_rsa_pss_verify_precomputed"
  sig := verifyPrecomputedMdTableSig
  writeArgs := true
  contracts := some fun A stack => verifyPrecomputedMdTableContract A stack
  summary := "RSASSA-PSS signature verification (RFC 8017 §8.1.2) with the hash function \
    of the table `hash` and MGF1 with that of the table `mgf1`, of a signature of a digest \
    of the former. With the modulus `n` (`n_len` bytes, most significant first, odd, from \
    512 to 8192 bits, its first byte not zero), " ++ exponentDoc ++ " and `pre`, the \
    `pre_len` words written by `vg_rsa_public_precompute` for `n` (returning 1), returns 1 \
    if `sig` (`n_len` bytes, most significant first) is an RSASSA-PSS signature of the \
    `digest_len`-byte digest `digest` with a salt of `salt_len` bytes, or of any length if \
    `any_salt_len` is not zero (BoringSSL's `RSA_PSS_SALTLEN_AUTO`); and 0 if it is not, or \
    if `n` is not such a modulus, `e` is not such a number, or `sig` is not below `n`. If \
    `pre` does not hold those values, the result is unspecified; memory safety and the \
    timing guarantee still apply.\n\n\
    Contract: `VG.Spec.RsaPss.verifyPrecomputedMdTableContract`. Constant time but for the \
    public key: timing may depend on the pointers, the lengths, `salt_len`, `any_salt_len`, \
    the contents of `n`, `e` and `pre`, and which tables `hash` and `mgf1` are, not on the \
    digest, the signature or anything computed from them but the result."
  safety := verifySafety ++ [digestLenSafety,
    "`pre_len` must be `2 * ⌈n_len / 8⌉`.",
    "For the result to be signature verification's, `pre` must hold what \
      `vg_rsa_public_precompute` wrote for `n` (returning 1).", hashSafety, mgf1Safety]

/-! ## `vg_rsa_pss_sign_precomputed` -/

/-- The parameters of `vg_rsa_pss_sign` with the key's precomputed values
`pre: *const u64, pre_len: usize` last. -/
def signPrecomputedMdTableSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("p", .slice false .u8 "p_len"),
    ("q", .slice false .u8 "q_len"), ("dp", .slice false .u8 "dp_len"),
    ("dq", .slice false .u8 "dq_len"), ("qinv", .slice false .u8 "qinv_len"),
    ("digest", .slice false .u8 "digest_len"), ("salt", .slice false .u8 "salt_len"),
    ("scratch", .slice true .u64 "scratch_len"), ("hash", MdHashTable.param),
    ("mgf1", MdHashTable.param), ("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- `signMdTableContract`, given the key's precomputed values `pre`
(`Rsa.privatePrecompute`): what `vg_rsa_pss_sign` computes, given `pre` holding
them. Constant time but for the public key and the modulus' values in
`pre`. -/
def signPrecomputedMdTableContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  signPrecomputedMdTableSig.contract A
    (pre := fun _out outLen n nLen _e eLen p pLen q qLen _dp dpLen _dq dqLen _qinv qinvLen
        _digest digestLen _salt _saltLen _scratch scratchLen hash _mgf1 pre preLen m =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.privatePrecomputedWords nLen.toNat pLen.toNat qLen.toNat ∧
        Rsa.privatePrecompute (bytesAt m n nLen.toNat) (bytesAt m p pLen.toNat)
          (bytesAt m q qLen.toNat) = some (Rsa.wordsAt m pre preLen.toNat) ∧
        digestLenOk A.ptrBits m hash digestLen)
    (post := fun out _outLen n nLen e eLen p pLen q qLen dp _dpLen dq _dqLen qinv _qinvLen
        digest _digestLen salt saltLen _scratch _scratchLen hash mgf1 _pre _preLen m m' r =>
      ∀ H G, MdHashTable.hashAt A.ptrBits m hash = some H →
        MdHashTable.hashAt A.ptrBits m mgf1 = some G →
        writtenOutcome m' out nLen.toNat r
          (sign H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m p pLen.toNat)
            (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat) (bytesAt m dq qLen.toNat)
            (bytesAt m qinv pLen.toNat) (bytesAt m digest H.len)
            (bytesAt m salt saltLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _p _pLen _q _qLen _dp _dpLen _dq _dqLen _qinv
        _qinvLen _digest _digestLen _salt _saltLen _scratch _scratchLen _hash _mgf1 pre _preLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        Rsa.privatePrecomputedLeak m pre nLen.toNat)

/-- `vg_rsa_pss_sign_precomputed` on every target. -/
def signPrecomputedMdTableApi : Api where
  module := "rsa_pss"
  name := "vg_rsa_pss_sign_precomputed"
  sig := signPrecomputedMdTableSig
  writeArgs := true
  contracts := some fun A stack => signPrecomputedMdTableContract A stack
  summary := "`vg_rsa_pss_sign`, given the key's precomputed values `pre`: computes and \
    returns what `vg_rsa_pss_sign` does with the same arguments. " ++
    Rsa.privatePrecomputedDoc ++ ".\n\n\
    Contract: `VG.Spec.RsaPss.signPrecomputedMdTableContract`. Constant time but for the \
    public key: timing may depend on the pointers, the lengths, the contents of `n` and `e`, \
    the first `2 * ⌈n_len / 8⌉` words of `pre` (the modulus' values), and which tables \
    `hash` and `mgf1` are, not on the private key, the rest of `pre`, the digest or the salt."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`.", "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`.",
    digestLenSafety] ++ scratchSafety ++ Rsa.privatePrecomputedSafety ++ [hashSafety, mgf1Safety]

end VG.Spec.RsaPss
