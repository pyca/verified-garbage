module

public import VerifiedGarbage.TCB.X86_64.Sse

/-!
# Streaming Merkle–Damgård hash functions on x86-64: the bytes of SSE registers

The 16 bytes of an SSE register (`vbytes`), as `finalize`'s padding
(`Impl.MdStream.X86_64.vecPad`) and the length fields (`lenV`) build them.
-/

@[expose] public section

namespace VG.Proof.MdStream.X86_64

open VG VG.X86_64

/-- The 16 bytes of `v`. -/
def vbytes (v : BitVec 128) : List Byte := (List.range 16).map (byte v)

theorem vbytes_length (v : BitVec 128) : (vbytes v).length = 16 := by simp [vbytes]

theorem vbytes_getElem (v : BitVec 128) {i : Nat} (hi : i < (vbytes v).length) :
    (vbytes v)[i] = byte v i := by simp [vbytes]

theorem byte_or (a b : BitVec 128) (i : Nat) : byte (a ||| b) i = byte a i ||| byte b i :=
  BitVec.extractLsb'_or

end VG.Proof.MdStream.X86_64
