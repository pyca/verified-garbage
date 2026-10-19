module
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Spec.ChaCha20.Contract


/-!
# ChaCha20 out of place

**Trusted** (as every file in `Spec/`). The keystream XORed into data read
from one buffer and written to another, for encryption out of place
(`Spec/ChaCha20Poly1305/OutOfPlace.lean`):

* `vg_chacha20_xor_to` is `vg_chacha20_xor` (`xorContract`) reading the
  data from `src` and writing the result to `dst`.
* `vg_chacha20_apply_to` is `vg_chacha20_apply` (`applyContract`) reading
  the data from `src` and writing the result to `dst`.
* `vg_chacha20_xor_split` is `vg_chacha20_xor` (`xorContract`) on the data
  in `dst` whose first `src_len` bytes are read from `src` instead: the
  first slice of a gathered plaintext encrypted out of place, the rest (a
  TLS record's content type) already copied after it in place, under one
  keystream, with no block of it split between two calls.

The output and the input are different buffers: the signatures make the
output overlap no other buffer (`Sig.contract`), so it never overlaps the
input; a caller XORing in place calls the functions of
`Spec/ChaCha20/Contract.lean`. Each output of `xor_to` and `apply_to` has
its own length argument, which the preconditions require to be the length
of the input; `xor_split`'s input from `src` is at most as long as its
output. The other arguments, what is public and what is secret (and what
`apply_to` may leak), and the working space are those of the functions they
follow. Existing contracts are unchanged.
-/

@[expose] public section

namespace VG.Spec.ChaCha20

/-- `vg_chacha20_xor_split(state: *mut [u32; 16], src: *const u8, src_len: usize, dst: *mut u8, len: usize, buf: *mut [u32; 80])`.
`state` is left unspecified, and `buf` is working space (as `xorSig`'s). -/
def xorSplitSig : Sig where
  params := [("state", .array true .u32 16), ("src", .slice false .u8 "src_len"),
    ("dst", .slice true .u8 "len"), ("buf", .array true .u32 80)]

/-- The input from `src` is at most as long as the output. -/
def xorSplitPre (pb : Nat) : Curry (xorSplitSig.words pb) (Mem → Prop) :=
  fun _state _src srcLen _dst len _buf _ => srcLen.toNat ≤ len.toNat

/-- For an input from `src` at most as long as the output (`xorSplitPre`):
writes to the `len` bytes at `dst` the `src_len` bytes at `src` followed by
the bytes at `dst` from `src_len` on, XORed with the first `len` bytes of
the keystream of the state at `state` (`xorContract`'s postcondition, with
the data's first `src_len` bytes read from `src`). The state (key, counter
and nonce) and the data are secret. -/
def xorSplitContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  xorSplitSig.contract A (pre := xorSplitPre A.ptrBits)
    (post := fun state src srcLen dst len _buf m m' _ =>
      bytesAt m' dst len.toNat =
        List.zipWith (· ^^^ ·)
          (bytesAt m src srcLen.toNat ++ (bytesAt m dst len.toNat).drop srcLen.toNat)
          (keystream (stateAt m state) len.toNat))
    (writeArgs := true)
    (stack := stack)

end VG.Spec.ChaCha20
