module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sym
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sym
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # Literals of the 16-bit inverse NTT of a polynomial stored with 16 bits, for the runs the kernel evaluates -/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Ntt16

materialize_value invTableHalves

end VG.Impl.MlKem.AArch64.Ntt16

namespace VG.Proof.MlKem.AArch64.NttR

open VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16

/-- The table of zetas of `nttInv`, halfword `i` the constant in lane
`i` (chunk `i / 8`'s lane `i % 8`). -/
def itabT : Nat := Impl.MlKem.AArch64.Ntt16.invTableHalves.foldr (fun h acc => cT h + 2 ^ tw * acc) 0

materialize_value itabT

/-- `nttInv` after the table (`halves`): the constants and the pointers, then the passes. -/
def invHead : List Instr :=
  qConsts ++ ([mov .x2 .x0, .addImm .x .x3 .x1 0, .addImm .x .x6 .x1 512, .movz .x .x5 8 0] : List Instr)

def invRest : Prog isa :=
  .seq (.loop (.block invPass1Body) (.nonzero .x .x5)) <|
  .seq (.block (invConsts ++ ([.addImm .x .x2 .x1 0, mov .x3 .x0, .movz .x .x5 4 0] : List Instr)))
    (.loop (.block invPass2Body) (.nonzero .x .x5))

def nttInvTail : Prog isa := .seq (.block invHead) invRest

materialize_code nttInvTail

end VG.Proof.MlKem.AArch64.NttR
