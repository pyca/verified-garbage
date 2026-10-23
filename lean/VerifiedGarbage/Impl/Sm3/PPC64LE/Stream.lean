module

public import VerifiedGarbage.Impl.Sm3.PPC64LE
public import VerifiedGarbage.Impl.MdStream.PPC64LE

/-!
# Streaming SM3: PPC64LE implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sm3.Repr`).

* `init(state = r3)` stores `IV`.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/PPC64LE.lean`), calling the compression function
  (`vg_sm3_compress`) with `scratch[0..112)` as its scratch space. The length
  field is big-endian, and so are the words of the hash value.
-/

@[expose] public section

namespace VG.Impl.Sm3.PPC64LE.Stream

open VG.PPC64LE
open VG.Impl.Sm3.PPC64LE (compress)

def init : Prog isa :=
  .block ((List.range 8).flatMap fun k =>
    [.lis .r8 (Spec.Sm3.iv[k]!.extractLsb' 16 16),
     .ori .r8 .r8 (Spec.Sm3.iv[k]!.extractLsb' 0 16),
     .store .w .r8 .r3 (4 * k)])

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/PPC64LE.lean`). -/

def params : MdStream.PPC64LE.Params where
  N := 32
  B := 64
  L := 8
  so := 112
  len := MdStream.PPC64LE.len64 88 true
  out := MdStream.PPC64LE.out32 8 true

def update : Prog isa := MdStream.PPC64LE.update params "vg_sm3_compress" compress

def finalize : Prog isa := MdStream.PPC64LE.finalize params "vg_sm3_compress" compress

end VG.Impl.Sm3.PPC64LE.Stream
