import VerifiedGarbage.Spec.Gcm.Precomputed

/-!
# AES-GCM encryption out of place

**Trusted** (as every file in `Spec/`). Encryption that reads the plaintext
from buffers of its own and writes the ciphertext to another, so that a
caller holding the plaintext in buffers it does not own (a TLS record layer,
which must write `ciphertext ‖ tag` to an output buffer) need not first copy
it there to encrypt it in place:

* `vg_aes_gcm_encrypt_blocks_to` is `vg_aes_gcm_encrypt_blocks`
  (`encryptBlocksContract`) reading the plaintext blocks from `src` and
  writing the ciphertext blocks to `dst`.
* `vg_aes_gcm_stream_encrypt_to` is `vg_aes_gcm_stream_encrypt`
  (`streamEncryptContract`) reading the next piece of plaintext from `src`
  and writing its encryption to `dst`.
* `vg_aes_gcm_seal_gather` is `vg_aes_gcm_seal` (`sealContract`) whose
  plaintext is the concatenation of a list of slices (`Param.slices`, read
  by `gathered`), as a vector of I/O buffers gives it: a record split into
  pieces, and TLS 1.3's content-type byte after it, are encrypted in one
  call, the ciphertext written to one buffer.
* `vg_aes_gcm_encrypt_blocks_to_precomputed`,
  `vg_aes_gcm_stream_encrypt_to_precomputed` and
  `vg_aes_gcm_seal_gather_precomputed` are the same with a key context of
  `vg_aes_gcm_init_precomputed`, as the `_precomputed` functions of
  `Spec/Gcm/Precomputed.lean` are those without it.

The output and the input are different buffers: the signatures make the
output overlap no other buffer (`Sig.contract`), so it never overlaps the
input; a caller encrypting in place calls the functions of
`Spec/Gcm/Contract.lean`. Each output has its own length argument, which
the preconditions require to be the length of the input. The other
arguments, what is public and what is secret, and the working space are
those of the functions they follow. Existing contracts are unchanged.
-/

namespace VG.Spec.Gcm

/-! ## Whole blocks -/

/-- `vg_aes_gcm_encrypt_blocks_to(ctx: *const [u64; 32], rounds: usize, counter: *mut [u8; 16], y: *mut [u8; 16], src: *const [u8; 16], n: usize, dst: *mut [u8; 16], dst_n: usize, scratch: *mut [u64; 264])`.
`rounds` is public; `scratch` is working space. -/
def encryptBlocksToSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("counter", .array true .u8 16), ("y", .array true .u8 16),
    ("src", .slice false (.array .u8 16) "n"), ("dst", .slice true (.array .u8 16) "dst_n"),
    ("scratch", .array true .u64 264)]

/-- `rounds` is 10, 12 or 14, and the output has as many blocks as the
input. -/
def encryptBlocksToPre (pb : Nat) : Curry (encryptBlocksToSig.words pb) (Mem → Prop) :=
  fun _ctx rounds _counter _y _src n _dst dstN _scratch _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ dstN = n

/-- With the key context at `ctx`: writes `C = ctr32 CIPH_K CB₁ P` to the
`n` blocks at `dst`, where `P` is the `n` blocks at `src` and `CB₁` the
block at `counter` (as `vg_aes_ctr32`), leaves `inc₃₂ⁿ(CB₁)` at `counter`,
and replaces the block `Y` at `y` with `GHASH_H` continued from `Y` over
`C` (as `vg_ghash`): `encryptBlocksContract`'s postcondition, with the
plaintext read from `src`. -/
def encryptBlocksToPost (pb : Nat) : encryptBlocksToSig.Post pb :=
  fun ctx rounds counter y src n dst _dstN _scratch m m' _ =>
    let c := ctr32 (ctxCiph m ctx rounds.toNat) (blockAt m counter) (blocksAt m src n.toNat)
    blocksAt m' dst n.toNat = c ∧
      blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter) ∧
      blockAt m' y = ghashFrom (ctxH m ctx) (blockAt m y) c

/-- For `rounds` of 10, 12 or 14 and as many blocks at `dst` as at `src`
(`encryptBlocksToPre`): `encryptBlocksToPost`. The key context, the
counter, `Y` and the data are secret. -/
def encryptBlocksToContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptBlocksToSig.contract A (pre := encryptBlocksToPre A.ptrBits)
    (post := encryptBlocksToPost A.ptrBits) (stack := stack)

/-- `vg_aes_gcm_encrypt_blocks_to` on every target. -/
def encryptBlocksToApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_encrypt_blocks_to"
  sig := encryptBlocksToSig
  contracts := some fun A stack => encryptBlocksToContract A stack
  summary := "AES-GCM's encryption of whole blocks (NIST SP 800-38D §7.1 steps 3 and 5, on whole \
    blocks), out of place: with the key context `*ctx` that `vg_aes_gcm_init` wrote for `rounds` \
    rounds, writes to the `n` 16-byte blocks at `dst` the `n` blocks at `src` XORed with \
    `CIPH_K(CB₁) … CIPH_K(CBₙ)`, where `CB₁` is the counter block `*counter` and \
    `CBᵢ₊₁ = inc₃₂(CBᵢ)`, leaves `inc₃₂ⁿ(CB₁)` in `*counter`, and replaces the block `Y` at `*y` \
    with GHASH (§6.4) continued from `Y` over the ciphertext written, with the hash subkey of \
    `*ctx`: `vg_aes_gcm_encrypt_blocks` with the plaintext read from `src`.\n\n\
    Contract: `VG.Spec.Gcm.encryptBlocksToContract`. Constant time: only the pointers, \
    `rounds` and `n` may affect timing, not the key context, the counter block, `Y` or the data."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "`dst_n` must equal `n`.",
    "The contents of `scratch` on return are unspecified."]

/-! ## Streaming -/

/-- `vg_aes_gcm_stream_encrypt_to(ctx: *const [u64; 32], rounds: usize, state: *mut [u64; 10], aad_len: u64, text_len: u64, src: *const u8, len: usize, dst: *mut u8, dst_len: usize)`.
`rounds`, `aad_len` and `text_len` are public. -/
def streamEncryptToSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("src", .slice false .u8 "len"), ("dst", .slice true .u8 "dst_len")]

/-- `rounds` is 10, 12 or 14, and the output is as long as the input. -/
def streamEncryptToPre (pb : Nat) : Curry (streamEncryptToSig.words pb) (Mem → Prop) :=
  fun _ctx rounds _state _aadLen _textLen _src len _dst dstLen _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ dstLen = len

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: if the
streaming state at `state` represents a message with the IV `iv`,
additional data `a` of `aad_len` bytes and the ciphertext of a plaintext
`p` of exactly `text_len` bytes (and `aad_len` modulo 2⁶⁴) so far, then
afterwards it represents the message with the ciphertext of `p` followed by
the `len` bytes at `src`, whose encryption is written to `dst`: the last
`len` bytes of `GCTR_K(inc₃₂(J₀), p ‖ src)`. (`streamEncryptPost`, with
the plaintext read from `src`.) -/
def streamEncryptToPost (pb : Nat) : streamEncryptToSig.Post pb :=
  fun ctx rounds state aadLen textLen src len dst _dstLen m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    let ciph := ctxCiph m ctx rounds.toNat
    let h := ctxH m ctx
    ∀ iv a p, StreamRepr m state ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      aadLen = BitVec.ofNat 64 a.length → textLen.toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ Aes.bytesAt m src len.toNat)
      StreamRepr m' state ciph h iv a c ∧ Aes.bytesAt m' dst len.toNat = c.drop p.length

/-- For `rounds` of 10, 12 or 14 and an output as long as the input
(`streamEncryptToPre`): `streamEncryptToPost`. -/
def streamEncryptToContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamEncryptToSig.contract A (pre := streamEncryptToPre A.ptrBits)
    (post := streamEncryptToPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_encrypt_to` on every target. -/
def streamEncryptToApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_encrypt_to"
  sig := streamEncryptToSig
  writeArgs := true
  contracts := some fun A stack => streamEncryptToContract A stack
  summary := "Encrypts the next piece of the text of an incremental AES-GCM encryption (NIST SP \
    800-38D §7.1), out of place: with the key context `*ctx` that `vg_aes_gcm_init` wrote for \
    `rounds` rounds, if the streaming state `*state` represents a message with `aad_len` bytes \
    of additional data and the ciphertext of exactly `text_len` bytes of plaintext so far, \
    writes to the `len` bytes at `dst` the encryption of the `len` bytes at `src`, as the \
    continuation of that plaintext, and the state then represents the message with them \
    appended: `vg_aes_gcm_stream_encrypt` with the plaintext read from `src`.\n\n\
    The function checks no length: GCM requires at most `2^36 - 32` bytes of text and at most \
    `2^61 - 1` bytes of additional data (§5.2.1.1), which the caller must check.\n\n\
    Contract: `VG.Spec.Gcm.streamEncryptToContract`. Constant time: only the pointers, \
    `rounds`, `aad_len`, `text_len` and `len` may affect timing, not the key context, the \
    state or the data."
  safety := ["`rounds` must be 10, 12 or 14.", "`dst_len` must equal `len`."]

/-! ## One-shot, from a list of slices -/

/-- The bytes of the slices that the `n` descriptors at `p` list in the
memory `m`, on a target with `ptrBits`-bit pointers, concatenated in order
(`Sig.listed`). -/
def gathered (ptrBits : Nat) (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (Sig.listed ptrBits m .u8 p n).flatMap fun r => Aes.bytesAt m r.base r.len

/-- The total length of the slices that the `n` descriptors at `p` list in
the memory `m`: the length of `gathered`. -/
def gatheredLen (ptrBits : Nat) (m : Mem) (p : Addr) (n : Nat) : Nat :=
  ((Sig.listed ptrBits m .u8 p n).map (·.len)).sum

/-- `vg_aes_gcm_seal_gather(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, src: *const [usize; 2], src_count: usize, dst: *mut u8, len: usize, tag: *mut [u8; 16])`.
`rounds` is public; `src` lists the pieces of the plaintext. -/
def sealGatherSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slices .u8 "src_count"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16)]

/-- `vg_aes_gcm_seal_gather`'s precondition: `rounds` is 10, 12 or 14, and
the slices `src` lists are `len` bytes long in all. -/
def sealGatherPre (pb : Nat) : Curry (sealGatherSig.words pb) (Mem → Prop) :=
  fun _ctx rounds _nonce _nonceLen _aad _aadLen src srcCount _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      gatheredLen pb m src srcCount.toNat = len.toNat

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`, and slices
of `len` bytes in all listed by `src`: the `len` bytes at `dst` are the
encryption of their concatenation (`gathered`), with the IV the `nonce_len`
bytes at `nonce` and the `aad_len` bytes of additional data at `aad`
(GCM-AE, `encryptWith`), and the 16-byte tag is at `tag`. (`sealPost`, with
the plaintext gathered from `src` and the ciphertext written to `dst`.) -/
def sealGatherPost (pb : Nat) : sealGatherSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    gatheredLen pb m src srcCount.toNat = len.toNat →
    encryptWith (ctxCiph m ctx rounds.toNat) (ctxH m ctx) 16 (Aes.bytesAt m nonce nonceLen.toNat)
        (gathered pb m src srcCount.toNat) (Aes.bytesAt m aad aadLen.toNat) =
      (Aes.bytesAt m' dst len.toNat, Aes.bytesAt m' tag 16)

/-- For `rounds` of 10, 12 or 14 and slices of `len` bytes in all
(`sealGatherPre`): `sealGatherPost`. -/
def sealGatherContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherSig.contract A (pre := sealGatherPre A.ptrBits) (post := sealGatherPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The documentation of the precondition on the slices `src` lists. -/
def gatherSafety : String :=
  "The slices `src` lists must be `len` bytes long in all."

/-- `vg_aes_gcm_seal_gather` on every target. -/
def sealGatherApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_gather"
  sig := sealGatherSig
  writeArgs := true
  contracts := some fun A stack => sealGatherContract A stack
  summary := "AES-GCM authenticated encryption (NIST SP 800-38D §7.1, GCM-AE, with a 128-bit \
    tag), out of place, of a plaintext in pieces: with the key context `*ctx` that \
    `vg_aes_gcm_init` wrote for `rounds` rounds, encrypts the concatenation of the \
    `src_count` slices that `src` lists (each an address and a length, in bytes), under the IV \
    the `nonce_len` bytes at `nonce`, writes the ciphertext to the `len` bytes at `dst`, and \
    writes the tag of the ciphertext and the `aad_len` bytes of additional data at `aad` to \
    `*tag`: `vg_aes_gcm_seal` with the plaintext gathered from `src`. A shorter tag is the \
    first bytes of this one.\n\n\
    The function checks no length. GCM is secure only for a nonce of 1 to `2^61 - 1` bytes, \
    at most `2^36 - 32` bytes of data and at most `2^61 - 1` bytes of additional data \
    (§5.2.1.1), which the caller must ensure; and a nonce must never be used twice with the \
    same key.\n\n\
    Contract: `VG.Spec.Gcm.sealGatherContract`. Constant time: only the pointers, `rounds`, \
    the lengths, `src_count` and where the slices are (their addresses and lengths) may \
    affect timing, not the key context, the nonce, the additional data or the data."
  safety := ["`rounds` must be 10, 12 or 14.", gatherSafety]

/-! ## With the powers of the hash subkey -/

/-- `vg_aes_gcm_encrypt_blocks_to_precomputed(ctx: *const [u64; 128], rounds: usize, counter: *mut [u8; 16], y: *mut [u8; 16], src: *const [u8; 16], n: usize, dst: *mut [u8; 16], dst_n: usize, scratch: *mut [u64; 264])`:
`encryptBlocksToSig` with the larger key context. -/
def encryptBlocksToPrecomputedSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("counter", .array true .u8 16), ("y", .array true .u8 16),
    ("src", .slice false (.array .u8 16) "n"), ("dst", .slice true (.array .u8 16) "dst_n"),
    ("scratch", .array true .u64 264)]

/-- `encryptBlocksToPre`, and the key context at `ctx` holds the powers of
its hash subkey. -/
def encryptBlocksToPrecomputedPre (pb : Nat) :
    Curry (encryptBlocksToPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _counter _y _src n _dst dstN _scratch m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ dstN = n ∧ PowersRepr m ctx

/-- `encryptBlocksToContract`, with the larger key context. -/
def encryptBlocksToPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptBlocksToPrecomputedSig.contract A (pre := encryptBlocksToPrecomputedPre A.ptrBits)
    (post := encryptBlocksToPost A.ptrBits) (stack := stack)

/-- `vg_aes_gcm_encrypt_blocks_to_precomputed` on every target. -/
def encryptBlocksToPrecomputedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_encrypt_blocks_to_precomputed"
  sig := encryptBlocksToPrecomputedSig
  contracts := some fun A stack => encryptBlocksToPrecomputedContract A stack
  summary := "`vg_aes_gcm_encrypt_blocks_to` with a key context of \
    `vg_aes_gcm_init_precomputed`: with the key context `*ctx` that \
    `vg_aes_gcm_init_precomputed` wrote for `rounds` rounds, does exactly what \
    `vg_aes_gcm_encrypt_blocks_to` does with its first 256 bytes (see \
    `vg_aes_gcm_encrypt_blocks_to`), and may read the powers of the hash subkey that it holds \
    instead of computing them. Its constant-time guarantee is \
    `vg_aes_gcm_encrypt_blocks_to`'s, the powers being as secret as the rest of the key \
    context.\n\n\
    Contract: `VG.Spec.Gcm.encryptBlocksToPrecomputedContract`."
  safety := encryptBlocksToApi.safety ++ [powersSafety]

/-- `vg_aes_gcm_stream_encrypt_to_precomputed(ctx: *const [u64; 128], rounds: usize, state: *mut [u64; 10], aad_len: u64, text_len: u64, src: *const u8, len: usize, dst: *mut u8, dst_len: usize)`:
`streamEncryptToSig` with the larger key context. -/
def streamEncryptToPrecomputedSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("src", .slice false .u8 "len"), ("dst", .slice true .u8 "dst_len")]

/-- `streamEncryptToPre`, and the key context at `ctx` holds the powers of
its hash subkey. -/
def streamEncryptToPrecomputedPre (pb : Nat) :
    Curry (streamEncryptToPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _state _aadLen _textLen _src len _dst dstLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ dstLen = len ∧
      PowersRepr m ctx

/-- `streamEncryptToContract`, with the larger key context. -/
def streamEncryptToPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamEncryptToPrecomputedSig.contract A (pre := streamEncryptToPrecomputedPre A.ptrBits)
    (post := streamEncryptToPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_encrypt_to_precomputed` on every target. -/
def streamEncryptToPrecomputedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_encrypt_to_precomputed"
  sig := streamEncryptToPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => streamEncryptToPrecomputedContract A stack
  summary := "`vg_aes_gcm_stream_encrypt_to` with a key context of \
    `vg_aes_gcm_init_precomputed`: with the key context `*ctx` that \
    `vg_aes_gcm_init_precomputed` wrote for `rounds` rounds, does exactly what \
    `vg_aes_gcm_stream_encrypt_to` does with its first 256 bytes (see \
    `vg_aes_gcm_stream_encrypt_to`), and may read the powers of the hash subkey that it holds \
    instead of computing them. Its constant-time guarantee is \
    `vg_aes_gcm_stream_encrypt_to`'s, the powers being as secret as the rest of the key \
    context.\n\n\
    Contract: `VG.Spec.Gcm.streamEncryptToPrecomputedContract`."
  safety := streamEncryptToApi.safety ++ [powersSafety]

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
    Curry (sealGatherPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen src srcCount _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      gatheredLen pb m src srcCount.toNat = len.toNat ∧ PowersRepr m ctx

/-- `sealGatherContract`, with the larger key context. -/
def sealGatherPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPrecomputedSig.contract A (pre := sealGatherPrecomputedPre A.ptrBits)
    (post := sealGatherPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_gather_precomputed` on every target. -/
def sealGatherPrecomputedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_gather_precomputed"
  sig := sealGatherPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => sealGatherPrecomputedContract A stack
  summary := "`vg_aes_gcm_seal_gather` with a key context of `vg_aes_gcm_init_precomputed`: \
    with the key context `*ctx` that `vg_aes_gcm_init_precomputed` wrote for `rounds` rounds, \
    does exactly what `vg_aes_gcm_seal_gather` does with its first 256 bytes (see \
    `vg_aes_gcm_seal_gather`), and may read the powers of the hash subkey that it holds \
    instead of computing them. Its constant-time guarantee is `vg_aes_gcm_seal_gather`'s, \
    the powers being as secret as the rest of the key context.\n\n\
    Contract: `VG.Spec.Gcm.sealGatherPrecomputedContract`."
  safety := sealGatherApi.safety ++ [powersSafety]

end VG.Spec.Gcm
