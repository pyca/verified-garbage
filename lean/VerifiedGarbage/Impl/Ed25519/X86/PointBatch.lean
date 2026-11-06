module

public import VerifiedGarbage.Impl.Ed25519.X86.PointPowers
public import VerifiedGarbage.Impl.Ed25519.X86.FieldMemory

/-! Rebuild a local batch while preserving the scalar accumulator. -/

@[expose] public section

namespace VG.Impl.Ed25519.X86
open VG.X86

def loadCheckpoint : List Instr := savePoint ++ tableAddr 1024 ++ pointFromTable
end VG.Impl.Ed25519.X86
