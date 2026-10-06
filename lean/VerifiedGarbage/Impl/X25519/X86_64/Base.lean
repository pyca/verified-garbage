import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed

/-! X25519(k, 9) with Ed25519's fixed-base comb and the map (Z + Y)/(Z - Y).
The expanded scalar is clamped as in RFC 7748 before the comb reads it. -/
namespace VG.Impl.X25519.X86_64.Base
open VG VG.X86_64 VG.Impl.Ed25519.X86_64

def clampBits : List Instr :=
  [.mov .rax (.imm 0), .store8 (sc 768) .rax, .store8 (sc 769) .rax,
    .store8 (sc 770) .rax, .store8 (sc 1023) .rax,
    .mov .rax (.imm 1), .store8 (sc 1022) .rax]

def uOps : List FieldOp := [.add 0 2 1, .sub 2 2 1]

def uEncode (fld : Arith) : Prog isa :=
  .seq (.block (fieldCode fld uOps)) (.seq (pointAffine fld) (.block (freeze 64)))

/-- The scalar's bits, clamped, `[k]B` by the comb `comb`, and its u-coordinate. -/
def engineOf (fld : Arith) (comb : Prog isa) : Prog isa :=
  .seq (scalarBasePrepare fld) (.seq (.block clampBits)
    (.seq comb (uEncode fld)))

def engine (fld : Arith) : Prog isa := engineOf fld (combMultiply fld)

def x25519Base (fld : Arith) : Prog isa := scalarBaseWith (engine fld)

/-- With the comb of AVX512_IFMA in `zmm` registers (`Ed25519.X86_64.Zmm.combMultiply`), and
BMI2's and ADX's field multiplications for the rest. -/
def x25519BaseIfma : Prog isa :=
  scalarBaseWith (engineOf VG.Impl.X25519.X86_64.adx (Zmm.combMultiply VG.Impl.X25519.X86_64.adx))

end VG.Impl.X25519.X86_64.Base
