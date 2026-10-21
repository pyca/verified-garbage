module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sym
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sym
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # Literals of the 16-bit NTT with an immutable table, for the runs the kernel evaluates -/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Ntt16.Readonly

materialize_code fwd
materialize_code fwdW

end VG.Impl.MlKem.AArch64.Ntt16.Readonly

namespace VG.Impl.MlKem.AArch64.Ntt16

materialize_value tableHalves

end VG.Impl.MlKem.AArch64.Ntt16

namespace VG.Proof.MlKem.AArch64.NttR

materialize_table zetaN 128

/-- The table of zetas of `fwd` and `fwdW`, halfword `i` the constant in lane
`i` (chunk `i / 8`'s lane `i % 8`). -/
def tabT : Nat := Impl.MlKem.AArch64.Ntt16.tableHalves.foldr (fun h acc => cT h + 2 ^ tw * acc) 0

materialize_value tabT

end VG.Proof.MlKem.AArch64.NttR

namespace VG.Proof.MlKem.AArch64.NttR

open VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16

/-- `ntt` after the table (`halves`): the constants and the pointers, then the passes. -/
def nttHead : List Instr := consts ++ ([mov .x2 .x0, .addImm .x .x3 .x1 0, .movz .x .x5 4 0] : List Instr)

def nttRest : Prog isa :=
  .seq (.loop (.block pass1Body) (.nonzero .x .x5)) <|
  .seq (.block [.addImm .x .x2 .x1 0, .addImm .x .x6 .x1 512, mov .x4 .x0, .movz .x .x5 8 0])
    (.loop (.block pass2Body) (.nonzero .x .x5))

def nttTail : Prog isa := .seq (.block nttHead) nttRest

materialize_code nttTail

end VG.Proof.MlKem.AArch64.NttR
