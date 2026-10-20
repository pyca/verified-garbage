module

public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey

/-! # Key generation with a supplied verified public-value exponentiator

The sampling and retry behavior is unchanged. Supplying the exponentiator
lets all arithmetic backends share its proof and callable Montgomery code.
-/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.KeyGenerate
open VG VG.Arm VG.Impl.Ffdh.Arm.Domain

/-- Finish one accepted scalar after its public value is computed. -/
def tail (power : Prog isa) : Prog isa := .seq power (.seq (inRange 6)
  (.seq (.block Exchange.saveResult) (.seq Exchange.exportResult GenerateKey.finish)))

def main (prepare tail : Prog isa) : Prog isa := .seq prepare (.seq GenerateKey.scalar
  (.seq (importAt 1 40 44) (.seq CheckPrivate.scalarRange (ifFlag tail GenerateKey.failScalar))))

def code (prepare tail : Prog isa) : Prog isa := framed (.seq (.block GenerateKey.entry) (head (main prepare tail)))

end VG.Impl.Ffdh.Arm.KeyGenerate
