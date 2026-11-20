module

public import VerifiedGarbage.Impl.Sm3.Arm
public import VerifiedGarbage.Impl.MdStream.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# Streaming SM3: 32-bit ARM implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sm3.Repr`).

* `init(state = r0)` stores `IV`.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/Arm.lean`), calling the compression function
  (`vg_sm3_compress`) with `scratch[0..104)` as its scratch space, and saving
  our caller's `r4`–`r11` and `lr` after it. The length field is big-endian,
  and so are the words of the hash value.
-/

@[expose] public section

namespace VG.Impl.Sm3.Arm.Stream

open VG.Arm
open VG.Impl.Sm3.Arm (compress)

def init : Prog isa :=
  .block ((List.range 8).flatMap fun k =>
    [.movw .r12 (Spec.Sm3.iv[k]!.extractLsb' 0 16),
     .movt .r12 (Spec.Sm3.iv[k]!.extractLsb' 16 16),
     .str .r12 .r0 (4 * k)])

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/Arm.lean`). -/

def params : MdStream.Arm.Params where
  N := 32
  B := 64
  L := 8
  so := 104
  len := MdStream.Arm.len64 88 true
  out := MdStream.Arm.out32 8 true

def update : Prog isa := MdStream.Arm.update params "vg_sm3_compress" compress

def finalize : Prog isa := MdStream.Arm.finalize params "vg_sm3_compress" compress

end VG.Impl.Sm3.Arm.Stream

/-! ## The functions as emitted

Each is its code, then its cleanup (`Impl/Residue/Arm.lean`): the registers
a callee may change set to constants, and for `update` and `finalize` first
the 168 bytes of their frame zeroed. None returns a value. -/

namespace VG.Impl.Sm3.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_sm3_init`. -/
def init : Prog isa := scrub 0 Stream.init

/-- `vg_sm3_update`: `Stream.update`, its scratch space in a frame of 168
bytes, which is then zeroed. -/
def update : Prog isa := scrubF 0 168 (Impl.StackScratch.Arm.withStackScratch 168 2 Stream.update)

/-- `vg_sm3_finalize`, as `update`. -/
def finalize : Prog isa := scrubF 0 168 (Impl.StackScratch.Arm.withStackScratch 168 1 Stream.finalize)

end VG.Impl.Sm3.Arm.Fn
