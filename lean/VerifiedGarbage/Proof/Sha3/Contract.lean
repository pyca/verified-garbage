module

public import VerifiedGarbage.Spec.Sha3.Contract
public import VerifiedGarbage.TCB.Artifact

/-!
# SHA-3 and SHAKE: the contracts of their internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The streaming sponge, `vg_keccak_absorb_scratch`, `vg_keccak_pad` and
`vg_keccak_squeeze` (on the representation `Repr`), in terms of
`Spec/Sha3.lean`, for any target: `A` is the target's calling convention,
and `stack` the number of bytes of stack below the stack pointer that an
implementation's calls and frames use (`Sig.contract`). A hash is computed
from the all-zero state (which represents the empty message) by
`vg_keccak_absorb_scratch` on each piece of the message, `vg_keccak_pad`,
and `vg_keccak_squeeze` from position 0: by the definitions, the output is
then `sponge rate suffix msg outlen`. Further calls of `vg_keccak_squeeze`,
each from the state and position the previous one left, output the bytes
that follow. They may overwrite their arguments passed in memory, where the
calling convention allows it (`writeArgs`). `scratch` is working space,
sized for the target with the fewest registers.

The permutation Keccak-f[1600] (`vg_keccak_f1600`), which the sponge
functions and the functions that run a sponge of their own call; and
`vg_keccak_pad_scratch` and `vg_keccak_squeeze_scratch`, `vg_keccak_pad`
and `vg_keccak_squeeze` with their working space passed in `scratch`, for
functions that call them with their own (the instances', ML-KEM's, ML-DSA's,
Ed448's), as `vg_keccak_absorb_scratch` is `vg_keccak_absorb`'s. The state
is secret; the rate, the position within the block and the
domain-separation suffix are public.
-/

@[expose] public section

namespace VG.Proof.Sha3

open VG.Spec.Sha3

/-- The arguments of `vg_keccak_absorb_scratch` but its working space,
`(state: *mut [u64; 25], rate: usize, pos: usize, data: *const u8, len: usize) -> usize`,
which `absorbPre` and `absorbPost` are stated over. `rate` and `pos` are
public. -/
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


/-- `vg_keccak_absorb_scratch(state: *mut [u64; 25], rate: usize, pos: usize, data: *const u8, len: usize, scratch: *mut [u64; 80]) -> usize`:
`absorbSig` with its working space passed in `scratch`. -/
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


/-- `vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut [u64; 64])`.
`scratch` is working space. -/
def permuteSig : Sig where
  params := [("state", .array true .u64 25), ("scratch", .array true .u64 64)]

/-- Applies Keccak-f[1600] to the state at `state`. The state is secret. -/
def permuteContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  permuteSig.contract A (post := fun state _scratch m m' _ =>
    stateAt m' state = keccakF (stateAt m state))
    (stack := stack)

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

end VG.Proof.Sha3
