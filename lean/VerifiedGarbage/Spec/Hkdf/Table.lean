module

public import VerifiedGarbage.Spec.Hkdf
public import VerifiedGarbage.Spec.HmacTable
public import VerifiedGarbage.TCB.Artifact

/-!
# HKDF with its HMAC given as a table: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_hkdf_extract` and
`vg_hkdf_expand`, in the module `hkdf`, compute HKDF-Extract and
HKDF-Expand (`Spec/Hkdf.lean`) with the hash function given at run time: a
last parameter `hmac`, a table of the interface `Hmac`
(`Spec/HmacTable.lean`), naming the hash function `H` (`HmacTable.hashAt`)
and the HMAC over it (`HmacTable.hmacOf H`, with `H`'s block size) that HKDF
uses, through the table's functions. So one function serves every hash
function, with every implementation of its HMAC, rather than a function
for each.

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

/-- `vg_hkdf_expand(prk: *const u8, prk_len: usize, info: *const u8, info_len: usize, out: *mut u8, out_len: usize, hmac: *const [usize; 6])`. -/
def expandSig : Sig where
  params := [("prk", .slice false .u8 "prk_len"), ("info", .slice false .u8 "info_len"),
    ("out", .slice true .u8 "out_len"), ("hmac", HmacTable.param)]

/-- `vg_hkdf_expand`'s precondition: the table names a hash function that
has an HMAC, and `out_len` is at most 255 of its digest lengths (so that
HKDF-Expand accepts it). -/
def expandPre (pb : Nat) : Curry (expandSig.words pb) (Mem → Prop) :=
  fun _prk _prkLen _info _infoLen _out outLen hmac m =>
    ∀ H, HmacTable.hashAt pb m hmac = some H →
      outLen.toNat ≤ 255 * H.len ∧ (HmacTable.hmacOf H).isSome

/-- For the hash function `H` the table at `hmac` names, writes
`HKDF-Expand(PRK, info, L)` with HMAC over it, of the `prk_len` bytes at
`prk` and the `info_len` bytes at `info`, with `L = out_len`, to the
`out_len` bytes at `out`. -/
def expandPost (pb : Nat) : expandSig.Post pb :=
  fun prk prkLen info infoLen out outLen hmac m m' _ =>
    ∀ H F, HmacTable.hashAt pb m hmac = some H → HmacTable.hmacOf H = some F →
      expand F H.len (bytesAt m prk prkLen.toNat) (bytesAt m info infoLen.toNat) outLen.toNat =
        some (bytesAt m' out outLen.toNat)

/-- If the table names a hash function with an HMAC and `out_len` is at most
255 of its digest lengths (`expandPre`): `expandPost`. The pseudorandom key,
the context information and the output keying material are secret. -/
def expandContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandSig.contract A (pre := expandPre A.ptrBits) (post := expandPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The `# Safety` item of `hmac`, for both functions. -/
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

/-- `vg_hkdf_expand` on every target. -/
def expandApi : Api where
  module := "hkdf"
  name := "vg_hkdf_expand"
  sig := expandSig
  writeArgs := true
  contracts := some fun A stack => expandContract A stack
  summary := "HKDF-Expand (RFC 5869 §2.3) with HMAC over the hash function of the table \
    `hmac`: writes the first `out_len` bytes of `T(1) ‖ T(2) ‖ …`, where \
    `T(i) = HMAC-Hash(PRK, T(i - 1) ‖ info ‖ i)`, `T(0)` is empty and `i` is one byte, of the \
    `prk_len` bytes `PRK` at `prk` and the `info_len` bytes `info` at `info`, to `out`. Calls \
    the table's verified HMAC functions.\n\n\
    Contract: `VG.Spec.Hkdf.expandContract`. Constant time: only the pointers, the lengths \
    and which table `hmac` is may affect timing, not the pseudorandom key, the context \
    information or the output keying material."
  safety := ["`out_len` must be at most 255 times the digest length of the hash function \
      `hmac` names.",
    hmacSafety]

end VG.Spec.Hkdf
