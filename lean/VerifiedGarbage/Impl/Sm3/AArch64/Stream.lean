import VerifiedGarbage.Impl.Sm3.AArch64
import VerifiedGarbage.Impl.MdStream.AArch64

/-!
# Streaming SM3: AArch64 implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sm3.Repr`).

* `init(state = x0)` stores `IV`.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/AArch64.lean`), calling the compression function
  (`vg_sm3_compress`) with `scratch[0..64)` as its scratch space. The length
  field is big-endian, and so are the words of the hash value.
-/

namespace VG.Impl.Sm3.AArch64.Stream

open VG.AArch64
open VG.Impl.Sm3.AArch64 (compress)

def init : Prog isa :=
  .block ((List.range 8).flatMap fun k =>
    [.movz .w .x9 (Spec.Sm3.iv[k]!.extractLsb' 0 16) 0,
     .movk .w .x9 (Spec.Sm3.iv[k]!.extractLsb' 16 16) 1,
     .str .w .x9 .x0 (4 * k)])

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/AArch64.lean`). -/

def params : MdStream.AArch64.Params where
  N := 32
  B := 64
  L := 8
  so := 64
  len := MdStream.AArch64.len64 88 true
  out := MdStream.AArch64.out32 8 true

def update : Prog isa := MdStream.AArch64.update params "vg_sm3_compress" compress

def finalize : Prog isa := MdStream.AArch64.finalize params "vg_sm3_compress" compress

end VG.Impl.Sm3.AArch64.Stream
