module

public import VerifiedGarbage.Impl.Ed25519.Arm.PointSelect
public import VerifiedGarbage.Impl.Ed25519.Arm.FieldMemory

/-! Descending scalar bits. Sixteen bits at workspace bytes 32–47 are
expanded from two scalar bytes for each checkpoint batch. -/

@[expose] public section

namespace VG.Impl.Ed25519.Arm
open VG.Arm

def scalarBitMask : List Instr :=
  [.dp .add .r2 .r0 (.reg .r11), .ldrb .r9 .r2 32, .dp .sub .r9 .r9 (.imm 1)]

end VG.Impl.Ed25519.Arm
