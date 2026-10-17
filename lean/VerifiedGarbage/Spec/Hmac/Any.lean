module

public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Spec.HashId

/-!
# HMAC and streaming hashing with the hash function as an argument: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `_scratch` functions of HMAC
(`Spec/Hmac/Generic.lean`) and the streaming `update` of its hash functions,
but with the hash function passed as a public `usize` argument, `hash`,
rather than fixed by the function's name: the number `HashId.hmac` gives it,
one of `hashIds` (SHA-1 and the SHA-2 functions; `inst` gives its
`Instance`), in the module `hash_any`:

* `vg_hmac_init_scratch`: `Instance.initScratchContract` of `inst hash`;
* `vg_hash_update_scratch`: the streaming `update` of `inst hash`'s hash
  function (`updatePost`), with which HMAC absorbs its text, and which any
  other caller of the streaming functions shares;
* `vg_hmac_finalize_scratch`: `Instance.finalizeScratchContract` of
  `inst hash`.

A function that takes the hash function as an argument calls these with it,
so that each of its calls of a streaming function is one call, and the
choice of the hash function's implementation is made here, once for all of
them.

Their buffers are as large as the largest hash function's: the streaming
states are `stateBytes` (192, SHA-512's), the digest `digestBytes` (64) and
the working space `scratchWords` (234 words, SHA-512's `Instance.scratch`).
Only their first bytes, as many as the hash function's, hold its states and
digest. That `hash` is in `hashIds` is a precondition; it is public (an
argument marked so, `Sig.contract`) and may affect timing.
-/

@[expose] public section

namespace VG.Spec.Hmac.Any

open Sha256 (bytesAt)

/-- The numbers (`HashId.hmac`) of the hash functions these functions take:
SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and SHA-512/256. -/
def hashIds : List Nat := [1, 2, 3, 4, 5, 6, 7]

/-- The hash function the number `i` names, as the HMAC contracts take it:
the `Instance` of `HashId.hmac i`, for SHA-1 and the SHA-2 functions. -/
def inst : Nat → Option Instance
  | 1 => some sha1I | 2 => some sha224I | 3 => some sha256I | 4 => some sha384I
  | 5 => some sha512I | 6 => some sha512_224I | 7 => some sha512_256I
  | _ => none

/-- The size of the streaming states: SHA-512's, the largest. -/
def stateBytes : Nat := 192

/-- The size of the digest buffer: SHA-512's, the largest. -/
def digestBytes : Nat := 64

/-- The words of working space: SHA-512's `Instance.scratch`, the most. -/
def scratchWords : Nat := 234

/-- The documentation's sentence on `hash`. -/
def hashDoc : String := s!"`hash` names the hash function: {HashId.sha12Doc}"

/-! ## `vg_hmac_init_scratch` -/

/-- `vg_hmac_init_scratch(inner: *mut [u8; 192], outer: *mut [u8; 192],
key: *const u8, key_len: usize, scratch: *mut [u64; 234], hash: usize)`. -/
def initSig : Sig where
  params := [("inner", .array true .u8 stateBytes), ("outer", .array true .u8 stateBytes),
    ("key", .slice false .u8 "key_len"), ("scratch", .array true .u64 scratchWords),
    ("hash", .int .usize true)]

/-- For the hash function `I` that `hash` names (`hashIds`) and a key of at
most its block size: `I`'s `initPost`, on the first bytes of `inner` and
`outer`. The key is secret. -/
def initContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initSig.contract A
    (pre := fun _inner _outer _key keyLen _scratch hash _ =>
      hash.toNat ∈ hashIds ∧ ∀ I, inst hash.toNat = some I → keyLen.toNat ≤ I.S.H.blockSize)
    (post := fun inner outer key keyLen _scratch hash m m' r =>
      ∀ I, inst hash.toNat = some I → initPost I.S A.ptrBits inner outer key keyLen m m' r)
    (writeArgs := true) (stack := stack)

/-- `vg_hmac_init_scratch` on every target. -/
def initApi : Api where
  module := "hash_any"
  name := "vg_hmac_init_scratch"
  sig := initSig
  writeArgs := true
  contracts := some fun A stack => initContract A stack
  summary := s!"`vg_hmac_<hash>_init_scratch` of the hash function `hash` names: starts an HMAC \
    computation with a key of at most the hash function's block size, making the streaming \
    state at the start of `*inner` represent `K₀ ⊕ ipad` and the one at the start of `*outer` \
    represent `K₀ ⊕ opad` (FIPS 198-1). The text is then absorbed with \
    `vg_hash_update_scratch` on `*inner` (its `count` starting at the block size), and the MAC \
    computed with `vg_hmac_finalize_scratch`, each with the same `hash`. {hashDoc}.\n\n\
    Contract: `VG.Spec.Hmac.Any.initContract`. Constant time: only the pointers, `key_len` \
    and `hash` may affect timing, not the key."
  safety := ["`hash` must be one of 1..=7.",
    "`key_len` must be at most the block size of `hash`'s hash function: 64 for SHA-1, \
      SHA-224 and SHA-256, 128 for the others.",
    "The contents of `scratch` on return are unspecified."]

/-! ## `vg_hash_update_scratch` -/

/-- `vg_hash_update_scratch(state: *mut [u8; 192], count: u64,
data: *const u8, len: usize, scratch: *mut [u64; 234], hash: usize)`. -/
def updateSig : Sig where
  params := [("state", .array true .u8 stateBytes), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 scratchWords),
    ("hash", .int .usize true)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴) for the hash function `S`, then afterwards it represents
`msg` followed by the `len` bytes at `data`: the streaming `update` of every
hash function's contract (`Spec/Sha256/Contract.lean`'s `updatePost`, …), as
HMAC's contracts represent its states (`StreamingHash.Repr`). -/
def updatePost {pb : Nat} (S : StreamingHash) (state : Addr) (count : BitVec 64) (data : Addr)
    (len : BitVec pb) (m m' : Mem) : Prop :=
  ∀ msg, S.Repr m state msg → count = BitVec.ofNat 64 msg.length →
    S.Repr m' state (msg ++ bytesAt m data len.toNat)

/-- For the hash function `I` that `hash` names (`hashIds`): `updatePost`.
The state and the data are secret. -/
def updateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateSig.contract A
    (pre := fun _state _count _data _len _scratch hash _ => hash.toNat ∈ hashIds)
    (post := fun state count data len _scratch hash m m' _ =>
      ∀ I, inst hash.toNat = some I → updatePost I.S state count data len m m')
    (writeArgs := true) (stack := stack)

/-- `vg_hash_update_scratch` on every target. -/
def updateApi : Api where
  module := "hash_any"
  name := "vg_hash_update_scratch"
  sig := updateSig
  writeArgs := true
  contracts := some fun A stack => updateContract A stack
  summary := s!"The streaming `update` of the hash function `hash` names, with its working \
    space in `*scratch`: if the streaming state at the start of `*state` represents a message \
    of `count` bytes (modulo 2⁶⁴), it then represents that message followed by the `len` \
    bytes at `data`. {hashDoc}.\n\n\
    Contract: `VG.Spec.Hmac.Any.updateContract`. Constant time: only the pointers, `count`, \
    `len` and `hash` may affect timing, not the state or the data."
  safety := ["`hash` must be one of 1..=7.",
    "The contents of `scratch` on return are unspecified."]

/-! ## `vg_hmac_finalize_scratch` -/

/-- `vg_hmac_finalize_scratch(inner: *mut [u8; 192], outer: *const [u8; 192],
count: u64, out: *mut [u8; 64], scratch: *mut [u64; 234], hash: usize)`. -/
def finalizeSig : Sig where
  params := [("inner", .array true .u8 stateBytes), ("outer", .array false .u8 stateBytes),
    ("count", .int .u64 true), ("out", .array true .u8 digestBytes),
    ("scratch", .array true .u64 scratchWords), ("hash", .int .usize true)]

/-- For the hash function `I` that `hash` names (`hashIds`): `I`'s
`finalizePost`, writing its MAC to the first bytes of `out`. The states are
secret. -/
def finalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeSig.contract A
    (pre := fun _inner _outer _count _out _scratch hash _ => hash.toNat ∈ hashIds)
    (post := fun inner outer count out _scratch hash m m' r =>
      ∀ I, inst hash.toNat = some I → finalizePost I.S A.ptrBits inner outer count out m m' r)
    (writeArgs := true) (stack := stack)

/-- `vg_hmac_finalize_scratch` on every target. -/
def finalizeApi : Api where
  module := "hash_any"
  name := "vg_hmac_finalize_scratch"
  sig := finalizeSig
  writeArgs := true
  contracts := some fun A stack => finalizeContract A stack
  summary := s!"`vg_hmac_<hash>_finalize_scratch` of the hash function `hash` names: finishes \
    an HMAC computation. If, for a key `K₀` of the hash function's block size and a text of \
    fewer than 2⁶⁴ bytes with the key, the streaming state at the start of `*inner` \
    represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes, and the one at the start of `*outer` \
    represents `K₀ ⊕ opad`, writes the HMAC of the text under `K₀` (as many bytes as the hash \
    function's digest) to the start of `*out`. {hashDoc}.\n\n\
    Contract: `VG.Spec.Hmac.Any.finalizeContract`. Constant time: only the pointers, `count` \
    and `hash` may affect timing, not the states."
  safety := ["`hash` must be one of 1..=7.",
    "The contents of `inner` on return are unspecified.",
    "The contents of `scratch` on return are unspecified."]

end VG.Spec.Hmac.Any
