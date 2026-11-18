module

public import VerifiedGarbage.Spec.Gcm.OutOfPlace

/-!
# AES-GCM with its key's bitsliced form kept apart from the key context

**Trusted.** A 1248-byte buffer holding two things computed once from a key
context (`KeyRepr`), for implementations that encrypt with bitsliced AES and
multiply in `GF(2¹²⁸)` with integer multiplications, which otherwise compute
them again, on the stack, at every call:

* bytes `64 j` to `64 j + 63`, for `j` from 0 to 14: the 16 bytes at byte
  `16 j` of the key context (round key `j` of its key schedule, for `j` up to
  its number of rounds) in the bitsliced layout of BearSSL's `aes_ct64`
  (Thomas Pornin), the block repeated four times (`SlicedKeyAt`): bit `t` of
  byte `i` of each of the four blocks `b` is bit `slicePos b i` of the
  little-endian 64-bit word at byte `8 t`;
* bytes 960 to 1247: 36 little-endian 64-bit words derived from the hash
  subkey `H` (`ghashOperand`, `ghashClass`): the two 64-bit words of
  `H · x⁻¹` and their sum, each split into its low and high 32 bits and their
  sum, each of those nine split into its four classes of bits modulo 4.

This is a storage convention, not a change to AES (FIPS 197) or to GCM's
field arithmetic (NIST SP 800-38D §6.3): the function that writes the buffer
(`vg_aes_gcm_bitslice`) and the functions that read it are proven against
the same definitions, and the latter's results against the unchanged GCM
postconditions, whatever the layout is.

`vg_aes_gcm_bitslice` computes the buffer from a key context alone, when the
key is set up. The `*_bitsliced` functions are `vg_aes_gcm_seal`,
`vg_aes_gcm_open`, `vg_aes_gcm_open_to`, `vg_aes_gcm_seal_gather` and the
streaming functions that also read the buffer, the key context and the
buffer through two pointers, as the `*_with_powers` functions do
(`Spec/Gcm/Powers8.lean`). They keep the existing GCM postconditions, memory
bounds, disjointness, leakage (`openLeak`, `openToLeak`) and secrecy
guarantees. The buffer is secret, as the key context is. They require the
buffer of the key context passed with them (`SlicedRepr`), so they have
names of their own. Existing specifications and contracts are unchanged.
-/

@[expose] public section

namespace VG.Spec.Gcm

/-! ## The buffer -/

/-- Bit `t` of byte `i = r + 4c` of block `b` (of four) is bit
`16r + 4c + b` of word `t`: the layout of BearSSL's `aes_ct64`. -/
def slicePos (b i : Nat) : Nat := 16 * (i % 4) + 4 * (i / 4) + b

/-- The eight little-endian 64-bit words at `p` hold the 16 bytes `rk` in
each of four blocks, bitsliced (`slicePos`). The four blocks and 16 bytes
cover the 64 bits of every word. -/
def SlicedKeyAt (m : Mem) (p : Addr) (rk : List Byte) : Prop :=
  ∀ t < 8, ∀ b < 4, ∀ i < 16,
    (m.readW (p + BitVec.ofNat 64 (8 * t)) 64).getLsbD (slicePos b i) = (rk.getD i 0).getLsbD t

/-- The first 64 bits of `H`, the coefficients of `x⁰` to `x⁶³` (§6.3), the
first the most significant. -/
def ghashHi (h : Block) : BitVec 64 := (h >>> 64).setWidth 64

/-- Its last 64 bits. -/
def ghashLo (h : Block) : BitVec 64 := h.setWidth 64

/-- The first word of `H · x⁻¹`: `H` shifted a bit towards `x⁰`, with
`x⁻¹ = 1 + x + x⁶ + x¹²⁷` added if its coefficient of `x⁰` was set. -/
def ghashKey0 (h : Block) : BitVec 64 :=
  ((ghashHi h <<< 1) ^^^ (ghashLo h >>> 63)) ^^^
    ((0#64 - (ghashHi h >>> 63)) &&& 0xc200000000000000#64)

/-- Its second word. -/
def ghashKey1 (h : Block) : BitVec 64 :=
  (ghashLo h <<< 1) ^^^ ((0#64 - (ghashHi h >>> 63)) &&& 1#64)

/-- Operand `i` (of 9) derived from `H`: of the word `ghashKey0 H`,
`ghashKey1 H` or their sum (`i / 3`), its low 32 bits, its high 32 bits or
their sum (`i % 3`), in the low 32 bits of a 64-bit word. -/
def ghashOperand (h : Block) (i : Nat) : BitVec 64 :=
  let w := if i / 3 = 0 then ghashKey0 h else if i / 3 = 1 then ghashKey1 h else
    ghashKey0 h ^^^ ghashKey1 h
  let lo := (w <<< 32) >>> 32
  let hi := w >>> 32
  if i % 3 = 0 then lo else if i % 3 = 1 then hi else lo ^^^ hi

/-- The bits of a 64-bit word whose position is `j` modulo 4. -/
def ghashClass (j : Nat) : BitVec 64 := 0x1111111111111111#64 <<< j

/-- The buffer at `bk` holds the bitsliced form of the 240 bytes `w` (each
of its 16-byte blocks at byte `64 j`, `SlicedKeyAt`) and, at byte
`960 + 8 (4 i + j)`, class `j` of operand `i` derived from the hash subkey
`h`. For a key context at `ctx`, `w` is its first 240 bytes (its key
schedule) and `h` its hash subkey (`ctxH`). -/
def SlicedRepr (m : Mem) (bk : Addr) (w : List Byte) (h : Block) : Prop :=
  (∀ j < 15, SlicedKeyAt m (bk + BitVec.ofNat 64 (64 * j)) (Aes.roundKey w j)) ∧
    ∀ i < 9, ∀ j < 4,
      m.readW (bk + BitVec.ofNat 64 (960 + 8 * (4 * i + j))) 64 = ghashOperand h i &&& ghashClass j

/-- `SlicedRepr` of the key context at `ctx`: its first 240 bytes and its
hash subkey. -/
def CtxSlicedRepr (m : Mem) (bk ctx : Addr) : Prop :=
  SlicedRepr m bk (Aes.bytesAt m ctx 240) (ctxH m ctx)

/-- The buffer written by `vg_aes_gcm_bitslice`. -/
def bitsliceParam : String × Param := ("bk", .array true .u64 156)

/-- The buffer read by the `*_bitsliced` functions. -/
def bitslicedParam : String × Param := ("bk", .array false .u64 156)

/-- Documentation shared by the `*_bitsliced` functions. -/
def bitslicedSummary (name contract : String) : String :=
  "`" ++ name ++ "` with the bitsliced form of the key context at `*bk` " ++
  "(`VG.Spec.Gcm.CtxSlicedRepr`), which it may read instead of computing it. Computes the same " ++
  "result as `" ++ name ++ "`. The buffer is secret, as the key context is: it may not " ++
  "affect timing; all other memory, aliasing and constant-time requirements are unchanged. " ++
  "Contract: `VG.Spec.Gcm." ++ contract ++ "`."

/-- What `*bk` must hold for the `*_bitsliced` functions. -/
def bitslicedSafety : String :=
  "`*bk` must be what `vg_aes_gcm_bitslice` wrote for the same key context (the \
    contract's precondition: `VG.Spec.Gcm.CtxSlicedRepr` of `bk` and the key context)."

/-! ## Writing the buffer -/

/-- `vg_aes_gcm_bitslice(ctx: *const [u64; 32], bk: *mut [u64; 156])`: a key
context and the buffer. -/
def bitsliceSig : Sig where
  params := [("ctx", .array false .u64 32), bitsliceParam]

/-- The bitsliced form of the key context at `ctx` at `bk`: of its first
240 bytes and of its hash subkey (its bytes 240–255, `ctxH`). -/
def bitslicePost (pb : Nat) : bitsliceSig.Post pb := fun ctx bk m m' _ =>
  SlicedRepr m' bk (Aes.bytesAt m ctx 240) (ctxH m ctx)

/-- No precondition: the buffer is that of whatever the context holds, as
for `storePowersContract`. -/
def bitsliceContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  bitsliceSig.contract A (post := bitslicePost A.ptrBits) (stack := stack)

/-- `vg_aes_gcm_bitslice` on every target. -/
def bitsliceApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_bitslice"
  sig := bitsliceSig
  contracts := some fun A stack => bitsliceContract A stack
  summary := "Writes to `*bk` the bitsliced form of the key context `*ctx` of \
    `vg_aes_gcm_init`: at byte `64*j`, for `j` from 0 to 14, its 16 bytes at byte `16*j` \
    (the round keys of its key schedule) in the bitsliced layout of BearSSL's `aes_ct64`, \
    and at byte 960 the 36 words derived from its hash subkey `H` (its bytes 240 to 255) that \
    GHASH's integer multiplications read (`VG.Spec.Gcm.SlicedRepr`), as the `*_bitsliced` \
    functions require for that key context. It reads only `*ctx` and writes only `*bk`. The \
    key context and the buffer are secret: only the pointers may affect timing.\n\n\
    Contract: `VG.Spec.Gcm.bitsliceContract`."
  safety := []

/-! ## One shot -/

/-- `vg_aes_gcm_seal_bitsliced(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *mut [u8; 16], bk: *const [u64; 156])`:
`sealSig` and the buffer. -/
def sealBitslicedSig : Sig where
  params := sealSig.params ++ [bitslicedParam]

/-- `sealPre`, and the bitsliced form of the key context at `bk`. -/
def sealBitslicedPre (pb : Nat) : Curry (sealBitslicedSig.words pb) (Mem → Prop) :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag bk m =>
    sealPre pb ctx rounds nonce nonceLen aad aadLen data len tag m ∧ CtxSlicedRepr m bk ctx

/-- `sealPost`, which does not depend on `bk`. -/
def sealBitslicedPost (pb : Nat) : sealBitslicedSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag _bk m m' r =>
    sealPost pb ctx rounds nonce nonceLen aad aadLen data len tag m m' r

/-- `sealBitslicedPre` and `sealBitslicedPost`. -/
def sealBitslicedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealBitslicedSig.contract A (pre := sealBitslicedPre A.ptrBits)
    (post := sealBitslicedPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_bitsliced` on every target. -/
def sealBitslicedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_bitsliced"
  sig := sealBitslicedSig
  writeArgs := true
  contracts := some fun A stack => sealBitslicedContract A stack
  summary := bitslicedSummary "vg_aes_gcm_seal" "sealBitslicedContract"
  safety := sealApi.safety ++ [bitslicedSafety]

/-- `vg_aes_gcm_open_bitsliced(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *const u8, tag_len: usize, bk: *const [u64; 156]) -> u32`:
`openSig` and the buffer. -/
def openBitslicedSig : Sig where
  params := openSig.params ++ [bitslicedParam]
  ret := some .u32

/-- `openPre`, and the bitsliced form of the key context at `bk`. -/
def openBitslicedPre (pb : Nat) : Curry (openBitslicedSig.words pb) (Mem → Prop) :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen bk m =>
    openPre pb ctx rounds nonce nonceLen aad aadLen data len tag tagLen m ∧ CtxSlicedRepr m bk ctx

/-- `openPost`, which does not depend on `bk`. -/
def openBitslicedPost (pb : Nat) : openBitslicedSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _bk m m' r =>
    openPost pb ctx rounds nonce nonceLen aad aadLen data len tag tagLen m m' r

/-- `openLeak`, which does not depend on `bk`. -/
def openBitslicedLeak (pb : Nat) : Curry (openBitslicedSig.words pb) (Mem → List Nat) :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _bk =>
    openLeak pb ctx rounds nonce nonceLen aad aadLen data len tag tagLen

/-- `openBitslicedPre`, `openBitslicedPost`, and what `openContract` may
leak (`openBitslicedLeak`). -/
def openBitslicedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openBitslicedSig.contract A (pre := openBitslicedPre A.ptrBits)
    (post := openBitslicedPost A.ptrBits) (writeArgs := true) (stack := stack)
    (leak := some (openBitslicedLeak A.ptrBits))

/-- `vg_aes_gcm_open_bitsliced` on every target. -/
def openBitslicedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_open_bitsliced"
  sig := openBitslicedSig
  writeArgs := true
  contracts := some fun A stack => openBitslicedContract A stack
  summary := bitslicedSummary "vg_aes_gcm_open" "openBitslicedContract"
  safety := openApi.safety ++ [bitslicedSafety]

/-- `vg_aes_gcm_open_to_bitsliced(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, src: *const u8, len: usize, dst: *mut u8, dst_len: usize, tag: *const u8, tag_len: usize, bk: *const [u64; 156]) -> u32`:
`openToSig` and the buffer. -/
def openToBitslicedSig : Sig where
  params := openToSig.params ++ [bitslicedParam]
  ret := some .u32

/-- `openToPre`, and the bitsliced form of the key context at `bk`. -/
def openToBitslicedPre (pb : Nat) : Curry (openToBitslicedSig.words pb) (Mem → Prop) :=
  fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen bk m =>
    openToPre pb ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen m ∧
      CtxSlicedRepr m bk ctx

/-- `openToPost`, which does not depend on `bk`. -/
def openToBitslicedPost (pb : Nat) : openToBitslicedSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _bk m m' r =>
    openToPost pb ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen m m' r

/-- `openToLeak`, which does not depend on `bk`. -/
def openToBitslicedLeak (pb : Nat) : Curry (openToBitslicedSig.words pb) (Mem → List Nat) :=
  fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _bk =>
    openToLeak pb ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen

/-- `openToBitslicedPre`, `openToBitslicedPost`, and what `openToContract`
may leak (`openToBitslicedLeak`). -/
def openToBitslicedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToBitslicedSig.contract A (pre := openToBitslicedPre A.ptrBits)
    (post := openToBitslicedPost A.ptrBits) (writeArgs := true) (stack := stack)
    (leak := some (openToBitslicedLeak A.ptrBits))

/-- `vg_aes_gcm_open_to_bitsliced` on every target. -/
def openToBitslicedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_open_to_bitsliced"
  sig := openToBitslicedSig
  writeArgs := true
  contracts := some fun A stack => openToBitslicedContract A stack
  summary := bitslicedSummary "vg_aes_gcm_open_to" "openToBitslicedContract"
  safety := openToApi.safety ++ [bitslicedSafety]

/-- `vg_aes_gcm_seal_gather_bitsliced(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, src: *const [usize; 2], src_count: usize, dst: *mut u8, len: usize, tag: *mut [u8; 16], bk: *const [u64; 156])`:
`sealGatherSig` and the buffer. -/
def sealGatherBitslicedSig : Sig where
  params := sealGatherSig.params ++ [bitslicedParam]

/-- `sealGatherPre`, and the bitsliced form of the key context at `bk`. -/
def sealGatherBitslicedPre (pb : Nat) : Curry (sealGatherBitslicedSig.words pb) (Mem → Prop) :=
  fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag bk m =>
    sealGatherPre pb ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag m ∧
      CtxSlicedRepr m bk ctx

/-- `sealGatherPost`, which does not depend on `bk`. -/
def sealGatherBitslicedPost (pb : Nat) : sealGatherBitslicedSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag _bk m m' r =>
    sealGatherPost pb ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag m m' r

/-- `sealGatherBitslicedPre` and `sealGatherBitslicedPost`. -/
def sealGatherBitslicedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherBitslicedSig.contract A (pre := sealGatherBitslicedPre A.ptrBits)
    (post := sealGatherBitslicedPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_gather_bitsliced` on every target. -/
def sealGatherBitslicedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_gather_bitsliced"
  sig := sealGatherBitslicedSig
  writeArgs := true
  contracts := some fun A stack => sealGatherBitslicedContract A stack
  summary := bitslicedSummary "vg_aes_gcm_seal_gather" "sealGatherBitslicedContract"
  safety := sealGatherApi.safety ++ [bitslicedSafety]

/-! ## Streaming -/

/-- `vg_aes_gcm_stream_init_bitsliced(ctx: *const [u64; 32], nonce: *const u8, nonce_len: usize, state: *mut [u64; 10], bk: *const [u64; 156])`:
`streamInitSig` and the buffer. -/
def streamInitBitslicedSig : Sig where
  params := streamInitSig.params ++ [bitslicedParam]

/-- The bitsliced form of the key context at `bk` (`streamInit` has no
other precondition). -/
def streamInitBitslicedPre (pb : Nat) : Curry (streamInitBitslicedSig.words pb) (Mem → Prop) :=
  fun ctx _nonce _nonceLen _state bk m => CtxSlicedRepr m bk ctx

/-- `streamInitPost`, which does not depend on `bk`. -/
def streamInitBitslicedPost (pb : Nat) : streamInitBitslicedSig.Post pb :=
  fun ctx nonce nonceLen state _bk m m' r => streamInitPost pb ctx nonce nonceLen state m m' r

/-- `streamInitBitslicedPre` and `streamInitBitslicedPost`. -/
def streamInitBitslicedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamInitBitslicedSig.contract A (pre := streamInitBitslicedPre A.ptrBits)
    (post := streamInitBitslicedPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_init_bitsliced` on every target. -/
def streamInitBitslicedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_init_bitsliced"
  sig := streamInitBitslicedSig
  writeArgs := true
  contracts := some fun A stack => streamInitBitslicedContract A stack
  summary := bitslicedSummary "vg_aes_gcm_stream_init" "streamInitBitslicedContract"
  safety := streamInitApi.safety ++ [bitslicedSafety]

/-- `vg_aes_gcm_stream_aad_bitsliced(ctx: *const [u64; 32], state: *mut [u64; 10], aad_len: u64, data: *const u8, len: usize, bk: *const [u64; 156])`:
`streamAadSig` and the buffer. -/
def streamAadBitslicedSig : Sig where
  params := streamAadSig.params ++ [bitslicedParam]

/-- The bitsliced form of the key context at `bk` (`streamAad` has no other
precondition). -/
def streamAadBitslicedPre (pb : Nat) : Curry (streamAadBitslicedSig.words pb) (Mem → Prop) :=
  fun ctx _state _aadLen _data _len bk m => CtxSlicedRepr m bk ctx

/-- `streamAadPost`, which does not depend on `bk`. -/
def streamAadBitslicedPost (pb : Nat) : streamAadBitslicedSig.Post pb :=
  fun ctx state aadLen data len _bk m m' r => streamAadPost pb ctx state aadLen data len m m' r

/-- `streamAadBitslicedPre` and `streamAadBitslicedPost`. -/
def streamAadBitslicedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamAadBitslicedSig.contract A (pre := streamAadBitslicedPre A.ptrBits)
    (post := streamAadBitslicedPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_aad_bitsliced` on every target. -/
def streamAadBitslicedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_aad_bitsliced"
  sig := streamAadBitslicedSig
  writeArgs := true
  contracts := some fun A stack => streamAadBitslicedContract A stack
  summary := bitslicedSummary "vg_aes_gcm_stream_aad" "streamAadBitslicedContract"
  safety := streamAadApi.safety ++ [bitslicedSafety]

/-- `vg_aes_gcm_stream_encrypt_bitsliced(ctx: *const [u64; 32], rounds: usize, state: *mut [u64; 10], aad_len: u64, text_len: u64, data: *mut u8, len: usize, bk: *const [u64; 156])`,
and `vg_aes_gcm_stream_decrypt_bitsliced` with the same signature:
`streamCryptSig` and the buffer. -/
def streamCryptBitslicedSig : Sig where
  params := streamCryptSig.params ++ [bitslicedParam]

/-- `streamTextPre`, and the bitsliced form of the key context at `bk`. -/
def streamTextBitslicedPre (pb : Nat) : Curry (streamCryptBitslicedSig.words pb) (Mem → Prop) :=
  fun ctx rounds state aadLen textLen data len bk m =>
    streamTextPre pb ctx rounds state aadLen textLen data len m ∧ CtxSlicedRepr m bk ctx

/-- `streamEncryptPost`, which does not depend on `bk`. -/
def streamEncryptBitslicedPost (pb : Nat) : streamCryptBitslicedSig.Post pb :=
  fun ctx rounds state aadLen textLen data len _bk m m' r =>
    streamEncryptPost pb ctx rounds state aadLen textLen data len m m' r

/-- `streamTextBitslicedPre` and `streamEncryptBitslicedPost`. -/
def streamEncryptBitslicedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptBitslicedSig.contract A (pre := streamTextBitslicedPre A.ptrBits)
    (post := streamEncryptBitslicedPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_encrypt_bitsliced` on every target. -/
def streamEncryptBitslicedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_encrypt_bitsliced"
  sig := streamCryptBitslicedSig
  writeArgs := true
  contracts := some fun A stack => streamEncryptBitslicedContract A stack
  summary := bitslicedSummary "vg_aes_gcm_stream_encrypt" "streamEncryptBitslicedContract"
  safety := streamEncryptApi.safety ++ [bitslicedSafety]

/-- `streamDecryptPost`, which does not depend on `bk`. -/
def streamDecryptBitslicedPost (pb : Nat) : streamCryptBitslicedSig.Post pb :=
  fun ctx rounds state aadLen textLen data len _bk m m' r =>
    streamDecryptPost pb ctx rounds state aadLen textLen data len m m' r

/-- `streamTextBitslicedPre` and `streamDecryptBitslicedPost`. -/
def streamDecryptBitslicedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptBitslicedSig.contract A (pre := streamTextBitslicedPre A.ptrBits)
    (post := streamDecryptBitslicedPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_decrypt_bitsliced` on every target. -/
def streamDecryptBitslicedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_decrypt_bitsliced"
  sig := streamCryptBitslicedSig
  writeArgs := true
  contracts := some fun A stack => streamDecryptBitslicedContract A stack
  summary := bitslicedSummary "vg_aes_gcm_stream_decrypt" "streamDecryptBitslicedContract"
  safety := streamDecryptApi.safety ++ [bitslicedSafety]

/-- `vg_aes_gcm_stream_finish_bitsliced(ctx: *const [u64; 32], rounds: usize, state: *mut [u64; 10], aad_len: u64, text_len: u64, tag: *mut [u8; 16], bk: *const [u64; 156])`:
`streamFinishSig` and the buffer. -/
def streamFinishBitslicedSig : Sig where
  params := streamFinishSig.params ++ [bitslicedParam]

/-- `streamFinishPre`, and the bitsliced form of the key context at `bk`. -/
def streamFinishBitslicedPre (pb : Nat) : Curry (streamFinishBitslicedSig.words pb) (Mem → Prop) :=
  fun ctx rounds state aadLen textLen tag bk m =>
    streamFinishPre pb ctx rounds state aadLen textLen tag m ∧ CtxSlicedRepr m bk ctx

/-- `streamFinishPost`, which does not depend on `bk`. -/
def streamFinishBitslicedPost (pb : Nat) : streamFinishBitslicedSig.Post pb :=
  fun ctx rounds state aadLen textLen tag _bk m m' r =>
    streamFinishPost pb ctx rounds state aadLen textLen tag m m' r

/-- `streamFinishBitslicedPre` and `streamFinishBitslicedPost`. -/
def streamFinishBitslicedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamFinishBitslicedSig.contract A (pre := streamFinishBitslicedPre A.ptrBits)
    (post := streamFinishBitslicedPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_finish_bitsliced` on every target. -/
def streamFinishBitslicedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_finish_bitsliced"
  sig := streamFinishBitslicedSig
  writeArgs := true
  contracts := some fun A stack => streamFinishBitslicedContract A stack
  summary := bitslicedSummary "vg_aes_gcm_stream_finish" "streamFinishBitslicedContract"
  safety := streamFinishApi.safety ++ [bitslicedSafety]

/-- `vg_aes_gcm_stream_verify_bitsliced(ctx: *const [u64; 32], rounds: usize, state: *mut [u64; 10], aad_len: u64, text_len: u64, tag: *const u8, tag_len: usize, bk: *const [u64; 156]) -> u32`:
`streamVerifySig` and the buffer. -/
def streamVerifyBitslicedSig : Sig where
  params := streamVerifySig.params ++ [bitslicedParam]
  ret := some .u32

/-- `streamVerifyPre`, and the bitsliced form of the key context at `bk`. -/
def streamVerifyBitslicedPre (pb : Nat) : Curry (streamVerifyBitslicedSig.words pb) (Mem → Prop) :=
  fun ctx rounds state aadLen textLen tag tagLen bk m =>
    streamVerifyPre pb ctx rounds state aadLen textLen tag tagLen m ∧ CtxSlicedRepr m bk ctx

/-- `streamVerifyPost`, which does not depend on `bk`. -/
def streamVerifyBitslicedPost (pb : Nat) : streamVerifyBitslicedSig.Post pb :=
  fun ctx rounds state aadLen textLen tag tagLen _bk m m' r =>
    streamVerifyPost pb ctx rounds state aadLen textLen tag tagLen m m' r

/-- `streamVerifyBitslicedPre` and `streamVerifyBitslicedPost`. -/
def streamVerifyBitslicedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamVerifyBitslicedSig.contract A (pre := streamVerifyBitslicedPre A.ptrBits)
    (post := streamVerifyBitslicedPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_verify_bitsliced` on every target. -/
def streamVerifyBitslicedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_verify_bitsliced"
  sig := streamVerifyBitslicedSig
  writeArgs := true
  contracts := some fun A stack => streamVerifyBitslicedContract A stack
  summary := bitslicedSummary "vg_aes_gcm_stream_verify" "streamVerifyBitslicedContract"
  safety := streamVerifyApi.safety ++ [bitslicedSafety]

end VG.Spec.Gcm
