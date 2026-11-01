module

public import VerifiedGarbage.Spec.Gcm.Prepared

/-!
# AES-GCM with eight prepared GHASH powers

Not trusted: the contracts of internal functions (`Rust.Internal`), which only verified code calls. A 384-byte key-context format for implementations that read only
the first eight prepared powers. The first 256 bytes are the existing key
context (`KeyRepr`'s layout: the key schedule, and the hash subkey at byte
240); the remaining 128 bytes hold 4 pairs, laid out exactly as the first 4
pairs of `PreparedPowersRepr` (bytes 256 through 383 of the 1024-byte
prepared format): pair `k` is `preparedPower(H^(2k+2))` then
`preparedPower(H^(2k+1))`, each stored little-endian. This is a storage
convention, not a change to GCM's field arithmetic (NIST SP 800-38D §6.3).

The context is not written from the key: `vg_aes_gcm_derive_prepared8` copies
an existing 256-byte key context and adds the powers of its hash subkey, so
it does not expand the key again. The 1024-byte prepared format
(`Spec/Gcm/Prepared.lean`) is unchanged, and remains the format of the
implementations that read all 48 powers.

These APIs have the existing GCM postconditions, memory bounds, disjointness
and secrecy guarantees. Their precondition differs from that of the
`*_prepared` APIs (`PreparedPowers8Repr` of a 384-byte context), so they have
distinct names: a 384-byte context must never be passed to a `*_prepared` or
`*_precomputed` API, which read up to 1024 bytes, or vice versa. The APIs that
read only the first 256 bytes (stream initialization, AAD, finish and verify)
remain usable. Existing specifications and contracts are unchanged.
-/

@[expose] public section

namespace VG.Proof.Gcm

open VG.Spec VG.Spec.Gcm

/-- The first 4 pairs of `PreparedPowersRepr`: pair `k`, at byte `256 + 32 k`,
contains the encoded `H^(2k+2)` then `H^(2k+1)`, each as a little-endian
128-bit word. The 4 pairs occupy bytes 256 through 383. -/
def PreparedPowers8Repr (m : Mem) (p : Addr) : Prop :=
  ∀ k < 4,
    m.readW (p + BitVec.ofNat 64 (256 + 32 * k)) 128 =
      preparedPower (hpow (ctxH m p) (2 * k + 2)) ∧
    m.readW (p + BitVec.ofNat 64 (272 + 32 * k)) 128 =
      preparedPower (hpow (ctxH m p) (2 * k + 1))

/-! ## The key context -/

/-- `vg_aes_gcm_derive_prepared8(src: *const [u64; 32], dst: *mut [u64; 48])`. -/
def derivePrepared8Sig : Sig where
  params := [("src", .array false .u64 32), ("dst", .array true .u64 48)]

/-- Copies the 256-byte key context at `src` to the first 256 bytes of `dst`,
and writes the first 8 prepared powers of its hash subkey after it. Only
these bytes of `src` matter: whatever `src` holds, the cipher (`ctxCiph`) and
hash subkey (`ctxH`) of `dst` become those of `src`. -/
def derivePrepared8Post (pb : Nat) : derivePrepared8Sig.Post pb := fun src dst m m' _ =>
  Aes.bytesAt m' dst 256 = Aes.bytesAt m src 256 ∧ PreparedPowers8Repr m' dst

/-- `derivePrepared8Post`, with no further precondition. -/
def derivePrepared8Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  derivePrepared8Sig.contract A (post := derivePrepared8Post A.ptrBits) (stack := stack)

/-! ## One-shot -/

/-- `vg_aes_gcm_seal_prepared8(ctx: *const [u64; 48], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *mut [u8; 16])`:
`sealSig` with the 384-byte key context. -/
def sealPrepared8Sig : Sig where
  params := [("ctx", .array false .u64 48), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .array true .u8 16)]

/-- The existing round-count requirement, plus the prepared powers. -/
def sealPrepared8Pre (pb : Nat) : Curry (sealPrepared8Sig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowers8Repr m ctx

/-- The unchanged `sealContract` postcondition with the 384-byte context. -/
def sealPrepared8Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPrepared8Sig.contract A (pre := sealPrepared8Pre A.ptrBits)
    (post := sealPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_open_prepared8(ctx: *const [u64; 48], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *const u8, tag_len: usize) -> u32`:
`openSig` with the 384-byte key context. -/
def openPrepared8Sig : Sig where
  params := [("ctx", .array false .u64 48), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice false .u8 "tag_len")]
  ret := some .u32

/-- The existing round-count requirement, plus the prepared powers. -/
def openPrepared8Pre (pb : Nat) : Curry (openPrepared8Sig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowers8Repr m ctx

/-- The unchanged `openContract` postcondition with the 384-byte context; it
may leak what `openContract` may (`openLeak`). -/
def openPrepared8Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPrepared8Sig.contract A (pre := openPrepared8Pre A.ptrBits)
    (post := openPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openLeak A.ptrBits))

/-- `vg_aes_gcm_seal_gather_prepared8(ctx: *const [u64; 48], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, src: *const [usize; 2], src_count: usize, dst: *mut u8, len: usize, tag: *mut [u8; 16])`:
`sealGatherSig` with the 384-byte key context. -/
def sealGatherPrepared8Sig : Sig where
  params := [("ctx", .array false .u64 48), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slices .u8 "src_count"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16)]

/-- The existing round-count and length requirements, plus the prepared powers. -/
def sealGatherPrepared8Pre (pb : Nat) : Curry (sealGatherPrepared8Sig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen src srcCount _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      gatheredLen pb m src srcCount.toNat = len.toNat ∧ PreparedPowers8Repr m ctx

/-- The unchanged `sealGatherContract` postcondition with the 384-byte context. -/
def sealGatherPrepared8Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPrepared8Sig.contract A (pre := sealGatherPrepared8Pre A.ptrBits)
    (post := sealGatherPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-! ## GHASH -/

/-- `vg_ghash_prepared8(h: *const [u8; 144], y: *mut [u8; 16], data: *const [u8; 16], n: usize, scratch: *mut [u64; 32])`:
`vg_ghash`'s signature, with `h` the last 144 bytes of a 384-byte prepared
key context (its hash subkey and 8 prepared powers). `scratch` is working
space. -/
def ghashPrepared8Sig : Sig where
  params := [("h", .array false .u8 144), ("y", .array true .u8 16),
    ("data", .slice false (.array .u8 16) "n"), ("scratch", .array true .u64 32)]

/-- `ghashContract`'s postcondition, for `h` at byte 240 of a context with
the 8 prepared powers (`PreparedPowers8Repr` of `h - 240`, whose hash subkey
`ctxH` is the block at `h`). -/
def ghashPrepared8Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ghashPrepared8Sig.contract A
    (pre := fun h _y _data _n _scratch m => PreparedPowers8Repr m (h - 240))
    (post := fun h y data n _scratch m m' _ =>
      blockAt m' y = ghashFrom (blockAt m h) (blockAt m y) (blocksAt m data n.toNat))
    (stack := stack)

end VG.Proof.Gcm
