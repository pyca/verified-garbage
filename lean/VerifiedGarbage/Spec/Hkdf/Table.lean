module

public import VerifiedGarbage.Spec.Hkdf
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Spec.HmacTable
public import VerifiedGarbage.TCB.Artifact

/-!
# HKDF with its HMAC given as a table: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_hkdf_extract`, `vg_hkdf_key`
and `vg_hkdf_expand`, in the module `hkdf`, compute HKDF-Extract and
HKDF-Expand (`Spec/Hkdf.lean`) with the hash function given at run time: a
last parameter `hmac`, a table of the interface `Hmac`
(`Spec/HmacTable.lean`), naming the hash function `H` (`HmacTable.hashAt`)
and the HMAC over it that HKDF uses, through the table's functions. So one
function serves every hash function, with every implementation of its HMAC,
rather than a function for each.

HKDF-Expand is usually run several times with one pseudorandom key (TLS 1.3
expands each secret into a key, an IV and the next secrets), so it is split
in two, as HMAC is: `vg_hkdf_key` keys HMAC with the pseudorandom key once,
writing HMAC's two streaming states for it (FIPS 198-1 §4 steps 1–3, as
`vg_hmac_<hash>_init`), and `vg_hkdf_expand` expands from those states,
which it only reads, so that each expansion hashes only its own blocks. The
states are those of the hash function's streaming implementation
(`streamingOf H`, `Spec/Hmac/Generic.lean`): the inner one at the start of
a 384-byte buffer, the outer one 192 bytes in (each at most 192 bytes,
`streamingOf_stateBytes`).

The lengths that depend on `H` are preconditions, on public lengths (which
table `hmac` is is public, `Abi.withTables`): `vg_hkdf_extract` writes a
`PRK` of exactly `H`'s digest length, and `vg_hkdf_expand` at most 255 of
them (§2.3).

`A` is the target's calling convention. The signatures fix where the
arguments are, the memory each function may access, disjointness, and that
the pointers and lengths are public (see `TCB/Sig.lean`); the contracts add
the rest: the contents of every buffer are secret, and the table's own
memory is read-only. The functions keep their working space on their own
stack: `stack` is the number of bytes below the stack pointer that an
implementation's calls and frames use (see `Sig.contract`). They may
overwrite their arguments passed in memory, where the calling convention
allows it (`writeArgs`), to pass arguments to the functions they call.
-/

@[expose] public section

namespace VG.Spec.Hkdf

open Sha256 (bytesAt)
open Mgf1 (Hash)
open Hmac (xorPad ipad opad blockKey)

/-! ## The streaming states of a table's hash function -/

/-- The streaming hash function `H` is, with HMAC over it (`Spec/Hmac.lean`)
and the streaming state of its verified functions (`Spec/Hmac/Generic.lean`),
if those give one (the hash functions of FIPS 180-4 and MD5); by `H`'s Rust
name, which is distinct for each. -/
def streamingOf (H : Hash) : Option Hmac.StreamingHash :=
  match H.rust with
  | "md5" => some Hmac.md5S
  | "sha1" => some Hmac.sha1S
  | "sha224" => some Hmac.sha224S
  | "sha256" => some Hmac.sha256S
  | "sha384" => some Hmac.sha384S
  | "sha512" => some Hmac.sha512S
  | "sha512_224" => some Hmac.sha512_224S
  | "sha512_256" => some Hmac.sha512_256S
  | _ => none

/-- The HMAC of a hash function's streaming form is the one the tables give
it (`HmacTable.hmacOf`). -/
theorem streamingOf_hmacOf (H : Hash) (S : Hmac.StreamingHash) (h : streamingOf H = some S) :
    HmacTable.hmacOf H = some S.H := by
  unfold streamingOf at h
  unfold HmacTable.hmacOf
  split at h <;> simp_all <;> subst h <;> rfl

/-- Each streaming state fits in its half of the 384-byte buffer. -/
theorem streamingOf_stateBytes (H : Hash) (S : Hmac.StreamingHash) (h : streamingOf H = some S) :
    S.stateBytes ≤ 192 := by
  unfold streamingOf at h
  split at h <;> simp_all <;> subst h <;> decide

/-- What a keyed buffer holds: at `key`, HMAC's inner streaming state of `S`
for the pseudorandom key `prk`, and 192 bytes in, the outer one. -/
def Keyed (S : Hmac.StreamingHash) (m : Mem) (key : Addr) (prk : List Byte) : Prop :=
  S.Repr m key (xorPad (blockKey S.H prk) ipad) ∧
    S.Repr m (key + BitVec.ofNat 64 192) (xorPad (blockKey S.H prk) opad)

/-! ## HKDF-Extract -/

/-- `vg_hkdf_extract(salt: *const u8, salt_len: usize, ikm: *const u8, ikm_len: usize, prk: *mut u8, prk_len: usize, hmac: *const [usize; 6])`. -/
def extractSig : Sig where
  params := [("salt", .slice false .u8 "salt_len"), ("ikm", .slice false .u8 "ikm_len"),
    ("prk", .slice true .u8 "prk_len"), ("hmac", HmacTable.param)]

/-- `vg_hkdf_extract`'s precondition: the table names a hash function that
has an HMAC, and `prk_len` is its digest length. -/
def extractPre (pb : Nat) : Curry (extractSig.words pb) (Mem → Prop) :=
  fun _salt _saltLen _ikm _ikmLen _prk prkLen hmac m =>
    ∀ H, HmacTable.hashAt pb m hmac = some H → prkLen.toNat = H.len ∧ (HmacTable.hmacOf H).isSome

/-- For the hash function `H` the table at `hmac` names, writes
`HKDF-Extract(salt, IKM)` with HMAC over it, of the `salt_len` bytes at
`salt` and the `ikm_len` bytes at `ikm`, to the `prk_len` (`H`'s digest
length) bytes at `prk`. -/
def extractPost (pb : Nat) : extractSig.Post pb :=
  fun salt saltLen ikm ikmLen prk _prkLen hmac m m' _ =>
    ∀ H F, HmacTable.hashAt pb m hmac = some H → HmacTable.hmacOf H = some F →
      bytesAt m' prk H.len = extract F (bytesAt m salt saltLen.toNat) (bytesAt m ikm ikmLen.toNat)

/-- If the table names a hash function with an HMAC and `prk_len` is its
digest length (`extractPre`): `extractPost`. The salt, the input keying
material and the pseudorandom key are secret. -/
def extractContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  extractSig.contract A (pre := extractPre A.ptrBits) (post := extractPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-! ## Keying HMAC with the pseudorandom key -/

/-- `vg_hkdf_key(prk: *const u8, prk_len: usize, key: *mut [u8; 384], hmac: *const [usize; 6])`. -/
def keySig : Sig where
  params := [("prk", .slice false .u8 "prk_len"), ("key", .array true .u8 384),
    ("hmac", HmacTable.param)]

/-- `vg_hkdf_key`'s precondition: the table names a hash function with a
streaming form (`streamingOf`). -/
def keyPre (pb : Nat) : Curry (keySig.words pb) (Mem → Prop) :=
  fun _prk _prkLen _key hmac m =>
    ∀ H, HmacTable.hashAt pb m hmac = some H → (streamingOf H).isSome

/-- For the hash function `H` the table at `hmac` names, makes the 384 bytes
at `key` hold HMAC's streaming states keyed with the `prk_len` bytes at
`prk` (`Keyed`). -/
def keyPost (pb : Nat) : keySig.Post pb :=
  fun prk prkLen key hmac m m' _ =>
    ∀ H S, HmacTable.hashAt pb m hmac = some H → streamingOf H = some S →
      Keyed S m' key (bytesAt m prk prkLen.toNat)

/-- If the table names a hash function with a streaming form (`keyPre`):
`keyPost`. The pseudorandom key and the states are secret. -/
def keyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  keySig.contract A (pre := keyPre A.ptrBits) (post := keyPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-! ## HKDF-Expand -/

/-- `vg_hkdf_expand(key: *const [u8; 384], info: *const u8, info_len: usize, out: *mut u8, out_len: usize, hmac: *const [usize; 6])`. -/
def expandSig : Sig where
  params := [("key", .array false .u8 384), ("info", .slice false .u8 "info_len"),
    ("out", .slice true .u8 "out_len"), ("hmac", HmacTable.param)]

/-- `vg_hkdf_expand`'s precondition: the table names a hash function with a
streaming form (`streamingOf`), and `out_len` is at most 255 of its digest
lengths (so that HKDF-Expand accepts it). -/
def expandPre (pb : Nat) : Curry (expandSig.words pb) (Mem → Prop) :=
  fun _key _info _infoLen _out outLen hmac m =>
    ∀ H, HmacTable.hashAt pb m hmac = some H →
      outLen.toNat ≤ 255 * H.len ∧ (streamingOf H).isSome

/-- For the hash function `H` the table at `hmac` names, if the 384 bytes at
`key` hold HMAC's streaming states keyed with a pseudorandom key `PRK`
(`Keyed`, as `vg_hkdf_key` writes them), writes `HKDF-Expand(PRK, info, L)`
with HMAC over `H`, of the `info_len` bytes at `info`, with `L = out_len`, to
the `out_len` bytes at `out`. -/
def expandPost (pb : Nat) : expandSig.Post pb :=
  fun key info infoLen out outLen hmac m m' _ =>
    ∀ H S prk, HmacTable.hashAt pb m hmac = some H → streamingOf H = some S → Keyed S m key prk →
      expand S.H H.len prk (bytesAt m info infoLen.toNat) outLen.toNat =
        some (bytesAt m' out outLen.toNat)

/-- If the table names a hash function with a streaming form and `out_len`
is at most 255 of its digest lengths (`expandPre`): `expandPost`. The
states, the context information and the output keying material are secret. -/
def expandContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandSig.contract A (pre := expandPre A.ptrBits) (post := expandPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-! ## The functions in the Rust interface -/

/-- The `# Safety` item of `hmac`, for each function. -/
def hmacSafety : String :=
  "`hmac` is a table of HMAC over the hash function HKDF uses: the one of \
    `VG.Spec.Mgf1.hashes` at the index in its first word of data (the HMAC tables of this \
    crate, `fn_tables`, say which they name)."

/-- `vg_hkdf_extract` on every target. -/
def extractApi : Api where
  module := "hkdf"
  name := "vg_hkdf_extract"
  sig := extractSig
  writeArgs := true
  contracts := some fun A stack => extractContract A stack
  summary := "HKDF-Extract (RFC 5869 §2.2) with HMAC over the hash function of the table \
    `hmac`: writes `PRK = HMAC-Hash(salt, IKM)` of the `salt_len` bytes at `salt` and the \
    `ikm_len` bytes at `ikm` to the `prk_len` bytes at `prk`, the hash function's digest \
    length. A salt that is not provided is the hash function's digest length of zero bytes \
    (or, equivalently, empty). Calls the table's verified HMAC functions.\n\n\
    Contract: `VG.Spec.Hkdf.extractContract`. Constant time: only the pointers, the lengths \
    and which table `hmac` is may affect timing, not the salt, the input keying material or \
    the pseudorandom key."
  safety := ["`prk_len` must be the digest length of the hash function `hmac` names.",
    hmacSafety]

/-- `vg_hkdf_key` on every target. -/
def keyApi : Api where
  module := "hkdf"
  name := "vg_hkdf_key"
  sig := keySig
  writeArgs := true
  contracts := some fun A stack => keyContract A stack
  summary := "Keys HMAC over the hash function of the table `hmac` with the pseudorandom key \
    `PRK`, the `prk_len` bytes at `prk`, for `vg_hkdf_expand`: makes the first bytes of \
    `*key` HMAC's inner streaming state for `PRK` and the bytes from its 192nd HMAC's outer \
    one (FIPS 198-1 §4, steps 1–3), through the table's `init`.\n\n\
    Contract: `VG.Spec.Hkdf.keyContract`. Constant time: only the pointers, `prk_len` and \
    which table `hmac` is may affect timing, not the pseudorandom key."
  safety := ["The other contents of `key` on return are unspecified; all of them may contain \
      secrets.",
    hmacSafety]

/-- `vg_hkdf_expand` on every target. -/
def expandApi : Api where
  module := "hkdf"
  name := "vg_hkdf_expand"
  sig := expandSig
  writeArgs := true
  contracts := some fun A stack => expandContract A stack
  summary := "HKDF-Expand (RFC 5869 §2.3) with HMAC over the hash function of the table \
    `hmac`, from HMAC keyed with the pseudorandom key `PRK` (`*key`, as `vg_hkdf_key` writes \
    it, which this only reads): writes the first `out_len` bytes of `T(1) ‖ T(2) ‖ …`, where \
    `T(i) = HMAC-Hash(PRK, T(i - 1) ‖ info ‖ i)`, `T(0)` is empty and `i` is one byte, of the \
    `info_len` bytes `info` at `info`, to `out`. Calls the table's verified HMAC functions.\n\n\
    Contract: `VG.Spec.Hkdf.expandContract`. Constant time: only the pointers, the lengths \
    and which table `hmac` is may affect timing, not the keyed states, the context \
    information or the output keying material."
  safety := ["`out_len` must be at most 255 times the digest length of the hash function \
      `hmac` names.",
    "`*key` must hold HMAC's streaming states keyed with a pseudorandom key for the hash \
      function `hmac` names, as `vg_hkdf_key` with the same table writes them; otherwise \
      what is written to `out` is unspecified.",
    hmacSafety]

end VG.Spec.Hkdf
