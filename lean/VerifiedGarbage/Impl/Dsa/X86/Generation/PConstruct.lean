module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PHash
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PShape
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PReduce

/-! A modulus candidate reuses the complete hash, byte-shaping, and arithmetic pipelines. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)

def pConstruct (H : Hash) (seedLen n : Nat) : Prog isa :=
  let count := (64 * n - 1) / (8 * H.D)
  .seq (pHashes H seedLen count)
    (.seq (pShape H.D count (8 * n)) (pReduce n H.D))

end VG.Impl.Dsa.X86.Generation
