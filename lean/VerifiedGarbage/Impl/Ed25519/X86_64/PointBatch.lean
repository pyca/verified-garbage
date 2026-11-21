module

public import VerifiedGarbage.Impl.Ed25519.X86_64.PointPowers
public import VerifiedGarbage.Impl.Ed25519.X86_64.FieldMemory

/-! Rebuild sixteen adjacent powers from a checkpoint, preserving the accumulator. -/

@[expose] public section

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

def loadCheckpoint (fld : Arith) : List Instr := savePoint fld ++ tableAddr 1280 ++ pointFromTable

end VG.Impl.Ed25519.X86_64
