import VerifiedGarbage.Impl.Ed25519.X86.InputBits
import VerifiedGarbage.Impl.Ed25519.X86.PointMul
import VerifiedGarbage.Impl.Ed25519.X86.PointEncode
import VerifiedGarbage.Impl.Ed25519.X86.Comb

namespace VG.Impl.Ed25519.X86
open VG VG.X86

/-! The address of the comb's tables at byte `combTbl` of the workspace, the scalar's bits,
one per byte at byte 7168, and `d` in slot 16; then the comb (`Comb.lean`) and the encoding. -/

def baseSetupOps : List FieldOp := [.const 16 Spec.Ed25519.d]

/-- After the tables' address. -/
def scalarBaseBody : Prog isa :=
  .seq (.block (abiSave 2 ++ inputBits 1 32 ++ fieldCode baseSetupOps))
    (.seq combMultiply (.seq pointEncode (.block (finishWords 96))))

def scalarBase : Code Instr Cond := .seq (combAddr 2) scalarBaseBody

end VG.Impl.Ed25519.X86
