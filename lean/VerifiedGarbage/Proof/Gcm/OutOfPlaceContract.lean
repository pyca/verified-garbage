module

public import VerifiedGarbage.Spec.Gcm.OutOfPlace
public import VerifiedGarbage.Proof.Gcm.Contract

/-!
# AES-GCM out of place: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.Gcm

open VG.Spec VG.Spec.Gcm

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

/-- `vg_aes_gcm_seal_split(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, src: *const u8, src_len: usize, dst: *mut u8, len: usize, tag: *mut [u8; 16])`.
`rounds` is public. -/
def sealSplitSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slice false .u8 "src_len"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16)]

/-- `rounds` is 10, 12 or 14, and the input from `src` is at most as long
as the output. -/
def sealSplitPre (pb : Nat) : Curry (sealSplitSig.words pb) (Mem → Prop) :=
  fun _ctx rounds _nonce _nonceLen _aad _aadLen _src srcLen _dst len _tag _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ srcLen.toNat ≤ len.toNat

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`, and an
input from `src` at most as long as the output: the `len` bytes at `dst` are
the encryption of the `src_len` bytes at `src` followed by the bytes at
`dst` from `src_len` on, with the IV the `nonce_len` bytes at `nonce` and the
`aad_len` bytes of additional data at `aad` (GCM-AE, `encryptWith`), and the
16-byte tag is at `tag`. (`sealPost`, with the data's first `src_len` bytes
read from `src`.) -/
def sealSplitPost (pb : Nat) : sealSplitSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src srcLen dst len tag m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    srcLen.toNat ≤ len.toNat →
    encryptWith (ctxCiph m ctx rounds.toNat) (ctxH m ctx) 16 (Aes.bytesAt m nonce nonceLen.toNat)
        (Aes.bytesAt m src srcLen.toNat ++ (Aes.bytesAt m dst len.toNat).drop srcLen.toNat)
        (Aes.bytesAt m aad aadLen.toNat) =
      (Aes.bytesAt m' dst len.toNat, Aes.bytesAt m' tag 16)

/-- For `rounds` of 10, 12 or 14 and an input from `src` at most as long as
the output (`sealSplitPre`): `sealSplitPost`. The key context, the nonce,
the additional data and the data are secret. -/
def sealSplitContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSplitSig.contract A (pre := sealSplitPre A.ptrBits) (post := sealSplitPost A.ptrBits)
    (writeArgs := true) (stack := stack)

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

/-- `vg_aes_gcm_seal_split_precomputed(ctx: *const [u64; 128], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, src: *const u8, src_len: usize, dst: *mut u8, len: usize, tag: *mut [u8; 16])`:
`sealSplitSig` with the larger key context. -/
def sealSplitPrecomputedSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slice false .u8 "src_len"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16)]

/-- `sealSplitPre`, and the key context at `ctx` holds the powers of its
hash subkey. -/
def sealSplitPrecomputedPre (pb : Nat) :
    Curry (sealSplitPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _src srcLen _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ srcLen.toNat ≤ len.toNat ∧
      PowersRepr m ctx

/-- `sealSplitContract`, with the larger key context. -/
def sealSplitPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSplitPrecomputedSig.contract A (pre := sealSplitPrecomputedPre A.ptrBits)
    (post := sealSplitPost A.ptrBits) (writeArgs := true) (stack := stack)

end VG.Proof.Gcm
