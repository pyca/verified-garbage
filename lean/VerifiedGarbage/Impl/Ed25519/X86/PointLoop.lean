import VerifiedGarbage.Impl.Ed25519.X86.FieldMemory

/-! Sixteen doublings with a public register counter. -/
namespace VG.Impl.Ed25519.X86
open VG.X86

def doubleBody : Prog isa := .seq pointDouble (.block [.alu .sub .esi (.imm 1)])
def double16 : Prog isa :=
  .seq (.block [.mov .esi (.imm 16)]) (.loop doubleBody .ne)

end VG.Impl.Ed25519.X86
