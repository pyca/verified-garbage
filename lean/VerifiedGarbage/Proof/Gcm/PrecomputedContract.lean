module

public import VerifiedGarbage.Spec.Gcm.OutOfPlace

/-! # The contracts of AES-GCM's functions with the powers in the key context

`vg_aes_gcm_init_precomputed`, `_seal_precomputed`, `_open_precomputed`,
`_stream_encrypt_precomputed`, `_stream_decrypt_precomputed`,
`_seal_gather_precomputed` and `_open_to_precomputed` take the 1024-byte key
context that also holds the powers of the hash subkey (`Spec.Gcm.PowersRepr`).
Only verified code calls them, so they are internal functions and their
contracts are here, not in `Spec/`. -/

@[expose] public section

namespace VG.Proof.Gcm

open VG.Spec.Gcm

/-- `vg_aes_gcm_init_precomputed(key: *const u8, key_len: usize, ctx: *mut [u64; 128])`. -/
def initPrecomputedSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 128)]

/-- Makes the 1024 bytes at `ctx` the key context of the key at `key`
(`KeyRepr`: its key schedule and its hash subkey `H = CIPH_K(0¹²⁸)`) with
the powers `H¹ … H⁴⁸` (`PowersRepr`). -/
def initPrecomputedPost (pb : Nat) : Proof.Gcm.initPrecomputedSig.Post pb := fun key keyLen ctx m m' _ =>
  KeyRepr m' ctx (Spec.Aes.bytesAt m key keyLen.toNat) ∧ PowersRepr m' ctx

/-- For a key of 16, 24 or 32 bytes (`initPre`): `Proof.Gcm.initPrecomputedPost`. -/
def initPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Proof.Gcm.initPrecomputedSig.contract A (pre := initPre A.ptrBits)
    (post := Proof.Gcm.initPrecomputedPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_precomputed(ctx: *const [u64; 128], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *mut [u8; 16])`:
`sealSig` with the larger key context. -/
def sealPrecomputedSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .array true .u8 16)]

/-- `rounds` is 10, 12 or 14, and the key context at `ctx` holds the powers
of its hash subkey. -/
def sealPrecomputedPre (pb : Nat) : Curry (Proof.Gcm.sealPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ PowersRepr m ctx

/-- `sealPost`, with the larger key context. -/
def sealPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Proof.Gcm.sealPrecomputedSig.contract A (pre := Proof.Gcm.sealPrecomputedPre A.ptrBits)
    (post := sealPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_open_precomputed(ctx: *const [u64; 128], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *const u8, tag_len: usize) -> u32`:
`openSig` with the larger key context. -/
def openPrecomputedSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice false .u8 "tag_len")]
  ret := some .u32

/-- `rounds` is 10, 12 or 14, and the key context at `ctx` holds the powers
of its hash subkey. -/
def openPrecomputedPre (pb : Nat) : Curry (Proof.Gcm.openPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ PowersRepr m ctx

/-- `openPost`, with the larger key context; it may leak what `openContract`
may (`openLeak`). -/
def openPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Proof.Gcm.openPrecomputedSig.contract A (pre := Proof.Gcm.openPrecomputedPre A.ptrBits)
    (post := openPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openLeak A.ptrBits))

/-- `vg_aes_gcm_stream_encrypt_precomputed(ctx: *const [u64; 128], rounds: usize, state: *mut [u64; 10], aad_len: u64, text_len: u64, data: *mut u8, len: usize)`,
and `vg_aes_gcm_stream_decrypt_precomputed` with the same signature:
`streamCryptSig` with the larger key context. -/
def streamCryptPrecomputedSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("data", .slice true .u8 "len")]

/-- `rounds` is 10, 12 or 14, and the key context at `ctx` holds the powers
of its hash subkey. -/
def streamTextPrecomputedPre (pb : Nat) :
    Curry (Proof.Gcm.streamCryptPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _state _aadLen _textLen _data _len m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ PowersRepr m ctx

/-- `streamEncryptPost`, with the larger key context. -/
def streamEncryptPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Proof.Gcm.streamCryptPrecomputedSig.contract A (pre := Proof.Gcm.streamTextPrecomputedPre A.ptrBits)
    (post := streamEncryptPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `streamDecryptPost`, with the larger key context. -/
def streamDecryptPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Proof.Gcm.streamCryptPrecomputedSig.contract A (pre := Proof.Gcm.streamTextPrecomputedPre A.ptrBits)
    (post := streamDecryptPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_gather_precomputed(ctx: *const [u64; 128], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, src: *const [usize; 2], src_count: usize, dst: *mut u8, len: usize, tag: *mut [u8; 16])`:
`sealGatherSig` with the larger key context. -/
def sealGatherPrecomputedSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slices .u8 "src_count"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16)]

/-- `sealGatherPre`, and the key context at `ctx` holds the powers of its
hash subkey. -/
def sealGatherPrecomputedPre (pb : Nat) :
    Curry (Proof.Gcm.sealGatherPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen src srcCount _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      gatheredLen pb m src srcCount.toNat = len.toNat ∧ PowersRepr m ctx

/-- `sealGatherContract`, with the larger key context. -/
def sealGatherPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Proof.Gcm.sealGatherPrecomputedSig.contract A (pre := Proof.Gcm.sealGatherPrecomputedPre A.ptrBits)
    (post := sealGatherPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_open_to_precomputed(ctx: *const [u64; 128], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, src: *const u8, len: usize, dst: *mut u8, dst_len: usize, tag: *const u8, tag_len: usize) -> u32`:
`openToSig` with the larger key context. -/
def openToPrecomputedSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slice false .u8 "len"), ("dst", .slice true .u8 "dst_len"),
    ("tag", .slice false .u8 "tag_len")]
  ret := some .u32

/-- `openToPre`, and the key context at `ctx` holds the powers of its hash
subkey. -/
def openToPrecomputedPre (pb : Nat) : Curry (Proof.Gcm.openToPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _src len _dst dstLen _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      dstLen.toNat = len.toNat ∧ PowersRepr m ctx

/-- `openToContract`, with the larger key context; it may leak what
`openToContract` may (`openToLeak`). -/
def openToPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Proof.Gcm.openToPrecomputedSig.contract A (pre := Proof.Gcm.openToPrecomputedPre A.ptrBits)
    (post := openToPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openToLeak A.ptrBits))

end VG.Proof.Gcm
