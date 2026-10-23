module

public import VerifiedGarbage.Impl.Sha1.PPC64LE
public import VerifiedGarbage.Impl.MdStream.PPC64LE

/-!
# Streaming SHA-1: PPC64LE implementation

The streaming state (84 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha1.Repr`).

* `init(state = r3)` stores `H⁽⁰⁾`.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/PPC64LE.lean`), calling the compression function
  (`vg_sha1_compress`).
-/

@[expose] public section

namespace VG.Impl.Sha1.PPC64LE.Stream

open VG.PPC64LE
open VG.Impl.Sha1.PPC64LE (compress)

def init : Prog isa :=
  .block ((List.range 5).flatMap fun k =>
    [.lis .r8 (Spec.Sha1.H0[k]!.extractLsb' 16 16),
     .ori .r8 .r8 (Spec.Sha1.H0[k]!.extractLsb' 0 16),
     .store .w .r8 .r3 (4 * k)])

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/PPC64LE.lean`). -/

def params : MdStream.PPC64LE.Params where
  N := 20
  B := 64
  L := 8
  so := 112
  len := MdStream.PPC64LE.len64 76 true
  out := MdStream.PPC64LE.out32 5 true

def update : Prog isa := MdStream.PPC64LE.update params "vg_sha1_compress" compress

def finalize : Prog isa := MdStream.PPC64LE.finalize params "vg_sha1_compress" compress

end VG.Impl.Sha1.PPC64LE.Stream
