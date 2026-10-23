module

public import VerifiedGarbage.Impl.Md5.PPC64LE
public import VerifiedGarbage.Impl.MdStream.PPC64LE

/-!
# Streaming MD5: PPC64LE implementation

The streaming state (80 bytes at `state`) is the MD buffer followed by a
64-byte buffer (see `VG.Spec.Md5.Repr`).

* `init(state = r3)` stores the initial MD buffer.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/PPC64LE.lean`), calling the compression function
  (`vg_md5_compress`).
-/

@[expose] public section

namespace VG.Impl.Md5.PPC64LE.Stream

open VG.PPC64LE
open VG.Impl.Md5.PPC64LE (compress)

def init : Prog isa :=
  .block ((List.range 4).flatMap fun k =>
    [.lis .r8 (Spec.Md5.H0[k]!.extractLsb' 16 16),
     .ori .r8 .r8 (Spec.Md5.H0[k]!.extractLsb' 0 16),
     .store .w .r8 .r3 (4 * k)])

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/PPC64LE.lean`). -/

def params : MdStream.PPC64LE.Params where
  N := 16
  B := 64
  L := 8
  so := 64
  len := MdStream.PPC64LE.len64 72 false
  out := MdStream.PPC64LE.out32 4 false

def update : Prog isa := MdStream.PPC64LE.update params "vg_md5_compress" compress

def finalize : Prog isa := MdStream.PPC64LE.finalize params "vg_md5_compress" compress

end VG.Impl.Md5.PPC64LE.Stream
