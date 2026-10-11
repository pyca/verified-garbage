module

public import VerifiedGarbage.Spec.ChaCha20.Contract

/-!
# ChaCha20 out of place

**Trusted** (as every file in `Spec/`). The keystream XORed into data read
from one buffer and written to another, for encryption out of place
(`Spec/ChaCha20Poly1305/OutOfPlace.lean`):

* `vg_chacha20_xor_to` is `vg_chacha20_xor` (`xorContract`) reading the
  data from `src` and writing the result to `dst`.
* `vg_chacha20_apply_to` is `vg_chacha20_apply` (`applyContract`) reading
  the data from `src` and writing the result to `dst`.

The output and the input are different buffers: the signatures make the
output overlap no other buffer (`Sig.contract`), so it never overlaps the
input; a caller XORing in place calls the functions of
`Spec/ChaCha20/Contract.lean`. Each output has its own length argument,
which the preconditions require to be the length of the input. The other
arguments, what is public and what is secret (and what `apply_to` may
leak), and the working space are those of the functions they follow.
Existing contracts are unchanged.
-/

@[expose] public section

namespace VG.Spec.ChaCha20

/-- `vg_chacha20_xor_to(state: *mut [u32; 16], src: *const u8, len: usize, dst: *mut u8, dst_len: usize, buf: *mut [u32; 80])`.
`state` is left unspecified, and `buf` is working space (as `xorSig`'s). -/
def xorToSig : Sig where
  params := [("state", .array true .u32 16), ("src", .slice false .u8 "len"),
    ("dst", .slice true .u8 "dst_len"), ("buf", .array true .u32 80)]

/-- The output is as long as the input. -/
def xorToPre (pb : Nat) : Curry (xorToSig.words pb) (Mem → Prop) :=
  fun _state _src len _dst dstLen _buf _ => dstLen = len

/-- For an output as long as the input (`xorToPre`): writes to the `len`
bytes at `dst` the `len` bytes at `src` XORed with the first `len` bytes of
the keystream of the state at `state` (`xorContract`'s postcondition, with
the data read from `src`). The state (key, counter and nonce) and the data
are secret. -/
def xorToContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  xorToSig.contract A (pre := xorToPre A.ptrBits)
    (post := fun state src len dst _dstLen _buf m m' _ =>
      bytesAt m' dst len.toNat =
        List.zipWith (· ^^^ ·) (bytesAt m src len.toNat) (keystream (stateAt m state) len.toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_chacha20_xor_to` on every target. -/
def xorToApi : Api where
  module := "chacha20"
  name := "vg_chacha20_xor_to"
  sig := xorToSig
  writeArgs := true
  contracts := some fun A stack => xorToContract A stack
  summary := "XORs the first `len` bytes of the ChaCha20 keystream of the 16-word state `*state` \
    (RFC 8439 §2.4: the block function of the state with its block counter, word 12, advanced by \
    0, 1, … modulo 2³²) into the `len` bytes at `src`, writing the result to the `len` bytes at \
    `dst`: `vg_chacha20_xor` out of place.\n\n\
    Contract: `VG.Spec.ChaCha20.xorToContract`. Constant time: only the pointers and `len` may \
    affect timing, not the state or the data."
  safety := [
    "`dst_len` must equal `len`.",
    "The contents of `state` on return are unspecified.",
    "The contents of `buf` on return are unspecified."]

/-- `vg_chacha20_apply_to(state: *mut [u64; 96], src: *const u8, len: usize, dst: *mut u8, dst_len: usize) -> u32`. -/
def applyToSig : Sig where
  params := [("state", .array true .u64 96), ("src", .slice false .u8 "len"),
    ("dst", .slice true .u8 "dst_len")]
  ret := some .u32

/-- The output is as long as the input. -/
def applyToPre (pb : Nat) : Curry (applyToSig.words pb) (Mem → Prop) :=
  fun _state _src len _dst dstLen _ => dstLen = len

/-- For an output as long as the input (`applyToPre`): if at least `len`
bytes of keystream are left in the streaming state at `state`, writes to the
`len` bytes at `dst` the `len` bytes at `src` XORed with the next `len` of
them, leaves the rest in the state, and returns 1. Otherwise returns 0,
leaving the output and what the state represents unchanged. The key is kept
either way. May leak the number of bytes of keystream left
(`applyContract`, with the data read from `src`). -/
def applyToContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  applyToSig.contract A (pre := applyToPre A.ptrBits)
    (post := fun state src len dst _dstLen m m' r =>
      keyAt m' state = keyAt m state ∧
        if len.toNat ≤ leftAt m state then
          r = 1 ∧
            bytesAt m' dst len.toNat =
              List.zipWith (· ^^^ ·) (bytesAt m src len.toNat) ((restAt m state).take len.toNat) ∧
            restAt m' state = (restAt m state).drop len.toNat
        else
          r = 0 ∧ bytesAt m' dst len.toNat = bytesAt m dst len.toNat ∧
            restAt m' state = restAt m state)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun state _src _len _dst _dstLen m => [leftAt m state])

/-- `vg_chacha20_apply_to` on every target. -/
def applyToApi : Api where
  module := "chacha20"
  name := "vg_chacha20_apply_to"
  sig := applyToSig
  writeArgs := true
  contracts := some fun A stack => applyToContract A stack
  summary := "Applies a ChaCha20 keystream (RFC 8439 §2.4) out of place: if at least `len` bytes \
    are left of the keystream that the streaming state `*state` represents, writes to the `len` \
    bytes at `dst` the `len` bytes at `src` XORed with the next `len` of them, keeps the rest in \
    `*state`, and returns 1. Otherwise (the block counter would pass 2³² − 1) returns 0, and \
    leaves the bytes at `dst` and the keystream unchanged: `vg_chacha20_apply` with the data \
    read from `src`.\n\n\
    Contract: `VG.Spec.ChaCha20.applyToContract`. Constant time: only the pointers, `len` and \
    the number of bytes of keystream left in `*state` (`VG.Spec.ChaCha20.leftAt`) may affect \
    timing, not the key, the nonce, the keystream or the data. The function may leak that \
    number."
  safety := ["`dst_len` must equal `len`."]

end VG.Spec.ChaCha20
