module

public import VerifiedGarbage.Impl.Bignum.Arm.SquareUmaal

/-! A shared square with a supplied reduction row; all other phases are unchanged. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def redRoundWith (rowCode : Prog isa) : Prog isa :=
  .seq (.block [.ldrSp .r0 0]) (.seq (.block redHeader) (.seq (.block redArgs) (.seq (.block redScalar)
    (.seq rowCode (.seq (.block [.ldrSp .r2 0]) (.seq (.block [.ldr .r2 .r2 80]) (.seq (.block redCarry)
      (.block sqCount))))))))

def redRoundsWith (rowCode : Prog isa) : Prog isa := .loop (redRoundWith rowCode) .ne

def sqReduceWith (rowCode : Prog isa) : Prog isa :=
  .seq (.seq sqAnchor (.block redInit)) (redRoundsWith rowCode)

def sqBodyReduceWith (rowCode : Prog isa) : Prog isa :=
  .seq sqInit (.seq crossRows (.seq sqDouble (.seq sqDiagU (.seq (sqReduceWith rowCode) sqFinish))))

def squareBodyReduceWith (rowCode : Prog isa) : Prog isa :=
  .seq (.block MontFn.bases) (sqBodyReduceWith rowCode)

end VG.Impl.Bignum.Arm
