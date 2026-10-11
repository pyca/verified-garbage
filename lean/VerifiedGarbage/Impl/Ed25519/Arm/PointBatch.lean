module

public import VerifiedGarbage.Impl.Ed25519.Arm.PointAccumulate

/-! Rebuild sixteen adjacent powers from a checkpoint while preserving the accumulator. -/

@[expose] public section

namespace VG.Impl.Ed25519.Arm
open VG.Arm

def loadCheckpoint : Prog isa := .seq savePoint (.block (tableAddr 1632 ++ pointFromTable))
def prepareBatch : Prog isa := .seq loadCheckpoint (.seq (pointPowers 5728 16 false) restorePoint)

end VG.Impl.Ed25519.Arm
