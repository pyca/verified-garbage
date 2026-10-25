module

public import VerifiedGarbage.Impl.MdStream.PPC64LE
public import VerifiedGarbage.Impl.Sha512.PPC64LE.Stream

/-!
# The SHA-512 family on PPC64LE, as Merkle–Damgård hash functions

The parameters of the generic Merkle–Damgård code (`Impl/MdStream/PPC64LE.lean`)
for SHA-512 (`mdParams`), SHA-384 (`mdParams384`), SHA-512/256
(`mdParams512_256`) and SHA-512/224 (`mdParams512_224`): a digest of the
first 8, 6 or 4 words of the hash value, or the first 3 and the high half of
the fourth (as the streaming `finalize` writes them, `outW` and `outHi`),
with the compression function `vg_sha512_compress`, which uses 176 bytes of
scratch space. PBKDF2's iteration (`Impl/Pbkdf2/PPC64LE.lean`) is built from
them; the streaming functions have code of their own (`Stream.lean`).
-/

@[expose] public section

namespace VG.Impl.Sha512.PPC64LE

def mdParams : MdStream.PPC64LE.Params where
  N := 64
  B := 128
  L := 16
  so := 176
  len := MdStream.PPC64LE.len128 176
  out := MdStream.PPC64LE.out64 8

def mdParams384 : MdStream.PPC64LE.Params := { mdParams with out := MdStream.PPC64LE.out64 6 }

def mdParams512_256 : MdStream.PPC64LE.Params := { mdParams with out := MdStream.PPC64LE.out64 4 }

def mdParams512_224 : MdStream.PPC64LE.Params :=
  { mdParams with out := MdStream.PPC64LE.out64 3 ++ Stream.outHi 3 }

end VG.Impl.Sha512.PPC64LE
