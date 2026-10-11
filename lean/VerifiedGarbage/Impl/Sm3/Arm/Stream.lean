import VerifiedGarbage.Impl.Sm3.Arm
import VerifiedGarbage.Impl.MdStream.Arm

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
