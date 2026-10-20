module

public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey

/-! Key generation with public sampling and exponentiation policies. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.SampleKeyGenerate
open VG VG.Arm VG.Impl.Ffdh.Arm.Domain

def main (prepare sample tail : Prog isa) : Prog isa :=
  .seq prepare (.seq sample (.seq (importAt 1 40 44)
    (.seq CheckPrivate.scalarRange (ifFlag tail GenerateKey.failScalar))))

def code (prepare sample tail : Prog isa) : Prog isa :=
  framed (.seq (.block GenerateKey.entry) (head (main prepare sample tail)))

end VG.Impl.Ffdh.Arm.SampleKeyGenerate
