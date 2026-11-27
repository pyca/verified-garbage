module

public import VerifiedGarbage.Impl.Ed25519.Arm.Power
public import VerifiedGarbage.Impl.Ed25519.Arm.Freeze

/-! Normalize extended coordinates, then form the compressed point in FR. -/

@[expose] public section

namespace VG.Impl.Ed25519.Arm
open VG.Arm

def affineOps : List FieldOp := [.mulc 0 0 15, .mulc 1 1 15]
def pointAffine (umaal : Bool) : Prog isa := .seq (invert umaal) (fieldCode umaal affineOps)

def pointSign : List Instr :=
  [.ldr .r3 .r0 FR, .dp .and .r10 .r3 (.imm 1), .mov .r10 (.shifted .r10 .lsl 15)]

def encodeSign : List Instr :=
  [.ldr .r3 .r0 (FR + 60), .dp .add .r3 .r3 (.reg .r10), .str .r3 .r0 (FR + 60)]

def pointEncode (umaal : Bool) : Prog isa :=
  .seq (pointAffine umaal) (.block (freeze 0 ++ pointSign ++ freeze 1 ++ encodeSign))

end VG.Impl.Ed25519.Arm
