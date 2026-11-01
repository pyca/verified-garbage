module

public import VerifiedGarbage.Spec.Blake2
public import VerifiedGarbage.TCB.Artifact

/-!
# BLAKE2b and BLAKE2s: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of streaming BLAKE2b
and BLAKE2s (`init`/`update`/`finalize`, on the representation `Repr`), in terms of `Spec/Blake2.lean`, for any
target: `A` is the target's calling convention. The signatures fix where the
arguments are, the memory each function may access, disjointness, and that
the pointers and lengths are public (see `TCB/Sig.lean`); the contracts add
the postconditions and which other arguments are public. States, keys and
messages are secret; the counts, the output length and the key length are
public.

A digest is computed by `init` with the output length `nn` and the key, which
makes the state represent `keyBlock w key` (the key padded to a block, or
nothing for unkeyed hashing), `update` on each piece of the message, and
`finalize`, whose first `nn` bytes of output are then `blake2 P nn key msg`
(for `1 ≤ nn ≤ P.maxBytes`, a key of at most `P.maxBytes` bytes, and data of
fewer than 2⁶⁴ bytes): `finalHash P (init P nn kk) (keyBlock w key ++ msg)`
takes its first `nn` bytes to the digest. The count the caller passes to
`update` and `finalize` is the length of the data so far, the key block
included.

`update` and `finalize` take the number of bytes of stack below the stack
pointer that an implementation's calls and frames use (`stack`, see
`Sig.contract`), 0 for one that uses none: it depends on the target, and on
which functions the implementation calls. They keep their working space
there.
-/

@[expose] public section

namespace VG.Spec.Blake2

/-! ## BLAKE2b -/

/-- `vg_blake2b_init(state: *mut [u8; 192], outlen: usize, key: *const u8, keylen: usize)`.
`outlen` is public. -/
def initBSig : Sig where
  params := [("state", .array true .u8 192), ("outlen", .int .usize true),
    ("key", .slice false .u8 "keylen")]

/-- For `1 ≤ outlen ≤ 64` and `keylen ≤ 64`: makes the streaming state at
`state` represent the key block of the `keylen` bytes at `key` (128 bytes, or
none if `keylen = 0`), hashed from the initial state for an `outlen`-byte
digest and a `keylen`-byte key. The key is secret. -/
def initBContract {M : ISA} (A : Abi M) : Contract M :=
  initBSig.contract A
    (pre := fun _state outlen _key keylen _ =>
      1 ≤ outlen.toNat ∧ outlen.toNat ≤ 64 ∧ keylen.toNat ≤ 64)
    (post := fun state outlen key keylen m m' _ =>
      Repr b (init b outlen.toNat keylen.toNat) m' state (keyBlock 64 (bytesAt m key keylen.toNat)))

/-- `vg_blake2b_init` on every target. -/
def initBApi : Api where
  module := "blake2b"
  name := "vg_blake2b_init"
  sig := initBSig
  contracts := some fun A _ => initBContract A
  summary := "Starts a BLAKE2b computation of an `outlen`-byte digest with the `keylen`-byte key \
    at `key` (none if `keylen` is 0): makes the streaming state `*state` represent the key padded \
    to a block, the first block of the data (none for unkeyed hashing), hashed from the initial \
    state for `outlen` and `keylen` (RFC 7693 §2.5, §3.3). The length of the data is then 128 if \
    `keylen > 0` and 0 otherwise. Continue with `vg_blake2b_update` and \
    `vg_blake2b_finalize`.\n\n\
    Contract: `VG.Spec.Blake2.initBContract`. The streaming state is the hash state followed by a \
    buffered last block (`VG.Spec.Blake2.Repr`). Constant time: only the pointers, `outlen` and \
    `keylen` may affect timing, not the key."
  safety := ["`outlen` must be between 1 and 64, and `keylen` at most 64."]

/-- `vg_blake2b_update(state: *mut [u8; 192], count: u64, data: *const u8, len: usize)`.
`count` is public. -/
def updateBSig : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("data", .slice false .u8 "len")]

/-- If the streaming state at `state` represents data `d` of `count` bytes
(modulo 2⁶⁴), hashed from any initial state, and `d` followed by the `len`
bytes at `data` is shorter than 2⁶⁴ bytes, then afterwards it represents that,
from the same initial state. -/
def updateBPost (pb : Nat) : updateBSig.Post pb := fun state count data len m m' _ =>
  ∀ h0 d, Repr b h0 m state d → count = BitVec.ofNat 64 d.length →
    d.length + len.toNat < 2 ^ 64 → Repr b h0 m' state (d ++ bytesAt m data len.toNat)

/-- `updateBPost`. The state and the data are secret. -/
def updateBContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateBSig.contract A (post := updateBPost A.ptrBits) (stack := stack)

/-- `vg_blake2b_update` on every target. -/
def updateBApi : Api where
  module := "blake2b"
  name := "vg_blake2b_update"
  sig := updateBSig
  contracts := some fun A stack => updateBContract A stack
  summary := "Absorbs data into a BLAKE2b computation: if the streaming state `*state` represents \
    data of `count` bytes, it then represents that data followed by the `len` bytes at `data`.\n\n\
    Contract: `VG.Spec.Blake2.updateBContract`. Constant time: only the pointers, `count` and `len` \
    may affect timing, not the state or the data."
  safety := [
    "`count` must be the exact length of the data so far (the key block included), and `count + \
      len` less than 2⁶⁴."]

/-- `vg_blake2b_finalize(state: *mut [u8; 192], count: u64, out: *mut [u8; 64])`.
`count` is public; `state` is left unspecified. -/
def finalizeBSig : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("out", .array true .u8 64)]

/-- If the streaming state at `state` represents data `d` of `count` bytes,
fewer than 2⁶⁴, hashed from the initial state `h0`, writes the final state of
`d` from `h0` (64 bytes; `finalHash b h0 d`) to `out`. The digest of `nn`
bytes is its first `nn` bytes. -/
def finalizeBPost (pb : Nat) : finalizeBSig.Post pb := fun state count out m m' _ =>
  ∀ h0 d, Repr b h0 m state d → d.length < 2 ^ 64 → count = BitVec.ofNat 64 d.length →
    bytesAt m' out 64 = finalHash b h0 d

/-- `finalizeBPost`. The state is secret. -/
def finalizeBContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeBSig.contract A (post := finalizeBPost A.ptrBits) (stack := stack)

/-- `vg_blake2b_finalize` on every target. -/
def finalizeBApi : Api where
  module := "blake2b"
  name := "vg_blake2b_finalize"
  sig := finalizeBSig
  contracts := some fun A stack => finalizeBContract A stack
  summary := "Finishes a BLAKE2b computation: if the streaming state `*state` represents data of \
    `count` bytes, compresses its last block and writes the final state `h[0..7]` (64 bytes) to \
    `*out`. The digest of `outlen` bytes (`init`'s) is its first `outlen` bytes.\n\n\
    Contract: `VG.Spec.Blake2.finalizeBContract`. Constant time: only the pointers and `count` may \
    affect timing, not the state."
  safety := [
    "`count` must be the exact length of the data (the key block included), less than 2⁶⁴.",
    "The contents of `state` on return are unspecified."]

/-! ## BLAKE2s -/

/-- `vg_blake2s_init(state: *mut [u8; 96], outlen: usize, key: *const u8, keylen: usize)`.
`outlen` is public. -/
def initSSig : Sig where
  params := [("state", .array true .u8 96), ("outlen", .int .usize true),
    ("key", .slice false .u8 "keylen")]

/-- For `1 ≤ outlen ≤ 32` and `keylen ≤ 32`: makes the streaming state at
`state` represent the key block of the `keylen` bytes at `key` (64 bytes, or
none if `keylen = 0`), hashed from the initial state for an `outlen`-byte
digest and a `keylen`-byte key. The key is secret. -/
def initSContract {M : ISA} (A : Abi M) : Contract M :=
  initSSig.contract A
    (pre := fun _state outlen _key keylen _ =>
      1 ≤ outlen.toNat ∧ outlen.toNat ≤ 32 ∧ keylen.toNat ≤ 32)
    (post := fun state outlen key keylen m m' _ =>
      Repr s (init s outlen.toNat keylen.toNat) m' state (keyBlock 32 (bytesAt m key keylen.toNat)))

/-- `vg_blake2s_init` on every target. -/
def initSApi : Api where
  module := "blake2s"
  name := "vg_blake2s_init"
  sig := initSSig
  contracts := some fun A _ => initSContract A
  summary := "Starts a BLAKE2s computation of an `outlen`-byte digest with the `keylen`-byte key \
    at `key` (none if `keylen` is 0): makes the streaming state `*state` represent the key padded \
    to a block, the first block of the data (none for unkeyed hashing), hashed from the initial \
    state for `outlen` and `keylen` (RFC 7693 §2.5, §3.3). The length of the data is then 64 if \
    `keylen > 0` and 0 otherwise. Continue with `vg_blake2s_update` and \
    `vg_blake2s_finalize`.\n\n\
    Contract: `VG.Spec.Blake2.initSContract`. The streaming state is the hash state followed by a \
    buffered last block (`VG.Spec.Blake2.Repr`). Constant time: only the pointers, `outlen` and \
    `keylen` may affect timing, not the key."
  safety := ["`outlen` must be between 1 and 32, and `keylen` at most 32."]

/-- `vg_blake2s_update(state: *mut [u8; 96], count: u64, data: *const u8, len: usize)`.
`count` is public. -/
def updateSSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("data", .slice false .u8 "len")]

/-- If the streaming state at `state` represents data `d` of `count` bytes
(modulo 2⁶⁴), hashed from any initial state, and `d` followed by the `len`
bytes at `data` is shorter than 2⁶⁴ bytes, then afterwards it represents that,
from the same initial state. -/
def updateSPost (pb : Nat) : updateSSig.Post pb := fun state count data len m m' _ =>
  ∀ h0 d, Repr s h0 m state d → count = BitVec.ofNat 64 d.length →
    d.length + len.toNat < 2 ^ 64 → Repr s h0 m' state (d ++ bytesAt m data len.toNat)

/-- `updateSPost`. The state and the data are secret. -/
def updateSContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateSSig.contract A (post := updateSPost A.ptrBits) (stack := stack)

/-- `vg_blake2s_update` on every target. -/
def updateSApi : Api where
  module := "blake2s"
  name := "vg_blake2s_update"
  sig := updateSSig
  contracts := some fun A stack => updateSContract A stack
  summary := "Absorbs data into a BLAKE2s computation: if the streaming state `*state` represents \
    data of `count` bytes, it then represents that data followed by the `len` bytes at `data`.\n\n\
    Contract: `VG.Spec.Blake2.updateSContract`. Constant time: only the pointers, `count` and `len` \
    may affect timing, not the state or the data."
  safety := [
    "`count` must be the exact length of the data so far (the key block included), and `count + \
      len` less than 2⁶⁴."]

/-- `vg_blake2s_finalize(state: *mut [u8; 96], count: u64, out: *mut [u8; 32])`.
`count` is public; `state` is left unspecified. -/
def finalizeSSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("out", .array true .u8 32)]

/-- If the streaming state at `state` represents data `d` of `count` bytes,
fewer than 2⁶⁴, hashed from the initial state `h0`, writes the final state of
`d` from `h0` (32 bytes; `finalHash s h0 d`) to `out`. The digest of `nn`
bytes is its first `nn` bytes. -/
def finalizeSPost (pb : Nat) : finalizeSSig.Post pb := fun state count out m m' _ =>
  ∀ h0 d, Repr s h0 m state d → d.length < 2 ^ 64 → count = BitVec.ofNat 64 d.length →
    bytesAt m' out 32 = finalHash s h0 d

/-- `finalizeSPost`. The state is secret. -/
def finalizeSContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeSSig.contract A (post := finalizeSPost A.ptrBits) (stack := stack)

/-- `vg_blake2s_finalize` on every target. -/
def finalizeSApi : Api where
  module := "blake2s"
  name := "vg_blake2s_finalize"
  sig := finalizeSSig
  contracts := some fun A stack => finalizeSContract A stack
  summary := "Finishes a BLAKE2s computation: if the streaming state `*state` represents data of \
    `count` bytes, compresses its last block and writes the final state `h[0..7]` (32 bytes) to \
    `*out`. The digest of `outlen` bytes (`init`'s) is its first `outlen` bytes.\n\n\
    Contract: `VG.Spec.Blake2.finalizeSContract`. Constant time: only the pointers and `count` may \
    affect timing, not the state."
  safety := [
    "`count` must be the exact length of the data (the key block included), less than 2⁶⁴.",
    "The contents of `state` on return are unspecified."]

end VG.Spec.Blake2
