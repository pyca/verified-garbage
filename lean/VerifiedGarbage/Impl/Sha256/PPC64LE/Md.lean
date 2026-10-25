module

public import VerifiedGarbage.Impl.MdStream.PPC64LE

/-!
# SHA-256 and SHA-224 on PPC64LE, as Merkle–Damgård hash functions

The parameters of the generic Merkle–Damgård code (`Impl/MdStream/PPC64LE.lean`)
for SHA-256 (`mdParams`) and SHA-224 (`mdParams224`, a digest of the first 7
words), with the compression function `vg_sha256_compress`, which uses 112
bytes of scratch space. PBKDF2's iteration (`Impl/Pbkdf2/PPC64LE.lean`) is
built from them; the streaming functions have code of their own
(`Stream.lean`).
-/

@[expose] public section

namespace VG.Impl.Sha256.PPC64LE

def mdParams : MdStream.PPC64LE.Params where
  N := 32
  B := 64
  L := 8
  so := 112
  len := MdStream.PPC64LE.len64 88 true
  out := MdStream.PPC64LE.out32 8 true

def mdParams224 : MdStream.PPC64LE.Params := { mdParams with out := MdStream.PPC64LE.out32 7 true }

end VG.Impl.Sha256.PPC64LE
