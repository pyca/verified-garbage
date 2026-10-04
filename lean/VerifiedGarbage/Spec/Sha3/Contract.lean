import VerifiedGarbage.Spec.Sha3
import VerifiedGarbage.TCB.Artifact

/-!
# SHA-3 and SHAKE: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of the permutation
Keccak-f[1600] and of the streaming sponge (`absorb`/`pad`/`squeeze`, on the
representation `Repr`), in terms of `Spec/Sha3.lean`, for any target: `A` is
the target's calling convention. The signatures fix where the arguments are,
the memory each function may access, disjointness, and that the pointers and
lengths are public (see `TCB/Sig.lean`); the contracts add the
postconditions and which other arguments are public. The state and the
message are secret; the rate, the position within the block and the
domain-separation suffix are public.

A hash is computed from the all-zero state (which represents the empty
message) by `vg_keccak_absorb` on each piece of the message,
`vg_keccak_pad`, and `vg_keccak_squeeze` from position 0: by the
definitions, the output is then `sponge rate suffix msg outlen`. Further
calls of `vg_keccak_squeeze`, each from the state and position the previous
one left, output the bytes that follow (for SHAKE). SHA3-224/256/384/512 use the rates
144, 136, 104 and 72 and the suffix `sha3Suffix`; SHAKE128 and SHAKE256 the
rates 168 and 136 and the suffix `shakeSuffix`.

The streaming functions take the number of bytes of stack below the stack
pointer that an implementation's calls and frames use (`stack`, see
`Sig.contract`), 0 for one that uses none: it depends on the target. They
may overwrite their arguments passed in memory, where the calling
convention allows it (`writeArgs`). `scratch` is working space, sized for
the target with the fewest registers. `vg_keccak_absorb`, `vg_keccak_pad` and
`vg_keccak_squeeze` keep theirs on the stack; `vg_keccak_absorb_scratch`,
`vg_keccak_pad_scratch` and `vg_keccak_squeeze_scratch` are the same
functions with theirs passed in `scratch`, for functions that call them with
their own (ML-KEM's, ML-DSA's, Ed448's).
-/

namespace VG.Spec.Sha3

/-- The rates, in bytes, of the six functions of FIPS 202 (§6). -/
def rates : List Nat := [72, 104, 136, 144, 168]

/-- `vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut [u64; 64])`.
`scratch` is working space. -/
def permuteSig : Sig where
  params := [("state", .array true .u64 25), ("scratch", .array true .u64 64)]

/-- Applies Keccak-f[1600] to the state at `state`. The state is secret. -/
def permuteContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  permuteSig.contract A (post := fun state _scratch m m' _ =>
    stateAt m' state = keccakF (stateAt m state))
    (stack := stack)

/-- `vg_keccak_f1600` on every target. -/
def permuteApi : Api where
  module := "sha3"
  name := "vg_keccak_f1600"
  sig := permuteSig
  contracts := some fun A stack => permuteContract A stack
  summary := "The permutation Keccak-f[1600] (FIPS 202 §3.4): applies it to the state `*state` \
    (lane `x + 5y` at index `x + 5y`).\n\n\
    Contract: `VG.Spec.Sha3.permuteContract`. Constant time: only the pointers may affect timing, \
    not the state."
  safety := ["The contents of `scratch` on return are unspecified."]

/-- `vg_keccak_absorb(state: *mut [u64; 25], rate: usize, pos: usize, data: *const u8, len: usize) -> usize`.
`rate` and `pos` are public. -/
def absorbSig : Sig where
  params := [("state", .array true .u64 25), ("rate", .int .usize true),
    ("pos", .int .usize true), ("data", .slice false .u8 "len")]
  ret := some .usize

/-- A rate in `rates`, and `pos < rate`. -/
def absorbPre (pb : Nat) : Curry (absorbSig.words pb) (Mem → Prop) :=
  fun _state rate pos _data _len _ => rate.toNat ∈ rates ∧ pos.toNat < rate.toNat

/-- If the state at `state` represents a message `msg` for `rate`, and `pos`
is the length of `msg` modulo `rate`, then afterwards it represents `msg`
followed by the `len` bytes at `data`. Returns `(pos + len) mod rate`, the
position after them. -/
def absorbPost (pb : Nat) : absorbSig.Post pb := fun state rate pos data len m m' ret =>
  (∀ msg, Repr m state rate.toNat msg → pos.toNat = msg.length % rate.toNat →
    Repr m' state rate.toNat (msg ++ bytesAt m data len.toNat)) ∧
  ret.toNat = (pos.toNat + len.toNat) % rate.toNat

/-- `absorbPre` and `absorbPost`. -/
def absorbContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  absorbSig.contract A (pre := absorbPre A.ptrBits) (post := absorbPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_keccak_absorb` on every target. -/
def absorbApi : Api where
  module := "sha3"
  name := "vg_keccak_absorb"
  sig := absorbSig
  writeArgs := true
  contracts := some fun A stack => absorbContract A stack
  summary := "Absorbs data into a SHA-3 or SHAKE computation: if the state `*state` represents a \
    message whose length is `pos` modulo `rate` (`VG.Spec.Sha3.Repr`), it then represents that \
    message followed by the `len` bytes at `data`. Returns the position after them, \
    `(pos + len) % rate`.\n\n\
    Contract: `VG.Spec.Sha3.absorbContract`. Constant time: only the pointers, `rate`, `pos` and \
    `len` may affect timing, not the state or the data."
  safety := ["`rate` must be 72, 104, 136, 144 or 168, and `pos` less than `rate`."]

/-- `vg_keccak_absorb_scratch(state: *mut [u64; 25], rate: usize, pos: usize, data: *const u8, len: usize, scratch: *mut [u64; 80]) -> usize`:
`vg_keccak_absorb` with its working space passed in `scratch`, for functions
that call it with theirs. -/
def absorbScratchSig : Sig where
  params := [("state", .array true .u64 25), ("rate", .int .usize true),
    ("pos", .int .usize true), ("data", .slice false .u8 "len"),
    ("scratch", .array true .u64 80)]
  ret := some .usize

/-- `absorbPre` and `absorbPost`, whatever `scratch` is. -/
def absorbScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  absorbScratchSig.contract A
    (pre := fun state rate pos data len _scratch => absorbPre A.ptrBits state rate pos data len)
    (post := fun state rate pos data len _scratch =>
      absorbPost A.ptrBits state rate pos data len)
    (writeArgs := true) (stack := stack)

/-- `vg_keccak_absorb_scratch` on every target. -/
def absorbScratchApi : Api where
  module := "sha3"
  name := "vg_keccak_absorb_scratch"
  sig := absorbScratchSig
  writeArgs := true
  contracts := some fun A stack => absorbScratchContract A stack
  summary := "`vg_keccak_absorb`, with its working space in `*scratch`.\n\n\
    Contract: `VG.Spec.Sha3.absorbScratchContract`. Constant time: only the pointers, `rate`, \
    `pos` and `len` may affect timing, not the state or the data."
  safety := [
    "`rate` must be 72, 104, 136, 144 or 168, and `pos` less than `rate`.",
    "The contents of `scratch` on return are unspecified."]

/-- `vg_keccak_pad(state: *mut [u64; 25], rate: usize, pos: usize, suffix: u32)`.
`rate`, `pos` and `suffix` are public. -/
def padSig : Sig where
  params := [("state", .array true .u64 25), ("rate", .int .usize true),
    ("pos", .int .usize true), ("suffix", .int .u32 true)]

/-- A rate in `rates`, and `pos < rate`. -/
def padPre (pb : Nat) : Curry (padSig.words pb) (Mem → Prop) :=
  fun _state rate pos _suffix _ => rate.toNat ∈ rates ∧ pos.toNat < rate.toNat

/-- If the state at `state` represents a message `msg` for `rate`, and `pos`
is the length of `msg` modulo `rate`, then afterwards it is the state after
absorbing `msg` padded with the domain-separation suffix `suffix` (its low
byte) and `pad10*1`. -/
def padPost (pb : Nat) : padSig.Post pb := fun state rate pos suffix m m' _ =>
  ∀ msg, Repr m state rate.toNat msg → pos.toNat = msg.length % rate.toNat →
    stateAt m' state = absorb rate.toNat (pad rate.toNat (suffix.setWidth 8) msg)

/-- `padPre` and `padPost`. -/
def padContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  padSig.contract A (pre := padPre A.ptrBits) (post := padPost A.ptrBits) (writeArgs := true)
    (stack := stack)

/-- `vg_keccak_pad` on every target. -/
def padApi : Api where
  module := "sha3"
  name := "vg_keccak_pad"
  sig := padSig
  writeArgs := true
  contracts := some fun A stack => padContract A stack
  summary := "Pads a SHA-3 or SHAKE message: if the state `*state` represents a message whose \
    length is `pos` modulo `rate` (`VG.Spec.Sha3.Repr`), it becomes the state after absorbing that \
    message with the domain-separation suffix (the low byte of `suffix`, with the first bit of the \
    padding: `0x06` for SHA-3, `0x1f` for SHAKE) and `pad10*1`.\n\n\
    Contract: `VG.Spec.Sha3.padContract`. Constant time: only the pointers, `rate`, `pos` and \
    `suffix` may affect timing, not the state."
  safety := ["`rate` must be 72, 104, 136, 144 or 168, and `pos` less than `rate`."]

/-- `vg_keccak_pad_scratch(state: *mut [u64; 25], rate: usize, pos: usize, suffix: u32, scratch: *mut [u64; 80])`:
`vg_keccak_pad` with its working space passed in `scratch`, for functions
that call it with theirs. -/
def padScratchSig : Sig where
  params := [("state", .array true .u64 25), ("rate", .int .usize true),
    ("pos", .int .usize true), ("suffix", .int .u32 true), ("scratch", .array true .u64 80)]

/-- `padPre` and `padPost`, whatever `scratch` is. -/
def padScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  padScratchSig.contract A
    (pre := fun state rate pos suffix _scratch => padPre A.ptrBits state rate pos suffix)
    (post := fun state rate pos suffix _scratch => padPost A.ptrBits state rate pos suffix)
    (writeArgs := true) (stack := stack)

/-- `vg_keccak_pad_scratch` on every target. -/
def padScratchApi : Api where
  module := "sha3"
  name := "vg_keccak_pad_scratch"
  sig := padScratchSig
  writeArgs := true
  contracts := some fun A stack => padScratchContract A stack
  summary := "`vg_keccak_pad`, with its working space in `*scratch`.\n\n\
    Contract: `VG.Spec.Sha3.padScratchContract`. Constant time: only the pointers, `rate`, `pos` \
    and `suffix` may affect timing, not the state."
  safety := [
    "`rate` must be 72, 104, 136, 144 or 168, and `pos` less than `rate`.",
    "The contents of `scratch` on return are unspecified."]

/-- `vg_keccak_squeeze(state: *mut [u64; 25], rate: usize, pos: usize, out: *mut u8, outlen: usize) -> usize`.
`rate` and `pos` are public. -/
def squeezeSig : Sig where
  params := [("state", .array true .u64 25), ("rate", .int .usize true),
    ("pos", .int .usize true), ("out", .slice true .u8 "outlen")]
  ret := some .usize

/-- A rate in `rates`, and `pos ≤ rate`. -/
def squeezePre (pb : Nat) : Curry (squeezeSig.words pb) (Mem → Prop) :=
  fun _state rate pos _out _outlen _ => rate.toNat ∈ rates ∧ pos.toNat ≤ rate.toNat

/-- Writes to `out` the `outlen` bytes of output (Algorithm 8, steps 7–10)
from the state at `state`, starting at byte `pos` of its output; and leaves
a state and returns a position from which the output continues after those
bytes. So output can be squeezed in pieces: from the state after `pad` and
position 0, then from each state and position a call leaves. -/
def squeezePost (pb : Nat) : squeezeSig.Post pb := fun state rate pos out outlen m m' ret =>
  bytesAt m' out outlen.toNat = squeezeFrom rate.toNat (stateAt m state) pos.toNat outlen.toNat ∧
  ret.toNat ≤ rate.toNat ∧
  ∀ d, squeezeFrom rate.toNat (stateAt m' state) ret.toNat d =
    squeezeFrom rate.toNat (stateAt m state) (pos.toNat + outlen.toNat) d

/-- `squeezePre` and `squeezePost`. -/
def squeezeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  squeezeSig.contract A (pre := squeezePre A.ptrBits) (post := squeezePost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_keccak_squeeze` on every target. -/
def squeezeApi : Api where
  module := "sha3"
  name := "vg_keccak_squeeze"
  sig := squeezeSig
  writeArgs := true
  contracts := some fun A stack => squeezeContract A stack
  summary := "Squeezes output from a padded SHA-3 or SHAKE state: writes to `out` the `outlen` \
    bytes of the output of the sponge with rate `rate` from the state `*state` (FIPS 202 Algorithm \
    8, steps 7 to 10), from byte `pos` of that output on; leaves in `*state` a state, and returns \
    a position, from which the output continues after them. Start from the state `vg_keccak_pad` \
    leaves and position 0.\n\n\
    Contract: `VG.Spec.Sha3.squeezeContract`. Constant time: only the pointers, `rate`, `pos` and \
    `outlen` may affect timing, not the state."
  safety := ["`rate` must be 72, 104, 136, 144 or 168, and `pos` at most `rate`."]

/-- `vg_keccak_squeeze_scratch(state: *mut [u64; 25], rate: usize, pos: usize, out: *mut u8, outlen: usize, scratch: *mut [u64; 80]) -> usize`:
`vg_keccak_squeeze` with its working space passed in `scratch`, for
functions that call it with theirs. -/
def squeezeScratchSig : Sig where
  params := [("state", .array true .u64 25), ("rate", .int .usize true),
    ("pos", .int .usize true), ("out", .slice true .u8 "outlen"),
    ("scratch", .array true .u64 80)]
  ret := some .usize

/-- `squeezePre` and `squeezePost`, whatever `scratch` is. -/
def squeezeScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  squeezeScratchSig.contract A
    (pre := fun state rate pos out outlen _scratch =>
      squeezePre A.ptrBits state rate pos out outlen)
    (post := fun state rate pos out outlen _scratch =>
      squeezePost A.ptrBits state rate pos out outlen)
    (writeArgs := true) (stack := stack)

/-- `vg_keccak_squeeze_scratch` on every target. -/
def squeezeScratchApi : Api where
  module := "sha3"
  name := "vg_keccak_squeeze_scratch"
  sig := squeezeScratchSig
  writeArgs := true
  contracts := some fun A stack => squeezeScratchContract A stack
  summary := "`vg_keccak_squeeze`, with its working space in `*scratch`.\n\n\
    Contract: `VG.Spec.Sha3.squeezeScratchContract`. Constant time: only the pointers, `rate`, \
    `pos` and `outlen` may affect timing, not the state."
  safety := [
    "`rate` must be 72, 104, 136, 144 or 168, and `pos` at most `rate`.",
    "The contents of `scratch` on return are unspecified."]

end VG.Spec.Sha3
