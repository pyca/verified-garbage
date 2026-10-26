module

public import VerifiedGarbage.Impl.TripleDes.RISCV64.Feistel
public import VerifiedGarbage.Proof.Framework.Bitslice.PosTable
public import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.Feistel
meta import VerifiedGarbage.Proof.Framework.Bitslice.PosTable
meta import VerifiedGarbage.Proof.Framework.Bitslice.Table
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
The round function's words of constants, its lanes' tables (each lane's
table in its block of 64 bits, `Bitslice.blocks`) and its three parts, as
literals.
-/

@[expose] public section

namespace VG.Impl.TripleDes.RISCV64

open VG.RISCV64

/-- The tables of the 64 lanes, each in its block of 64 bits. -/
def laneTables : Nat := VG.Bitslice.blocks 64 (fun p => VG.Bitslice.tableOf (laneBit p) 64) 64

materialize_value roundConsts
materialize_value laneTables

materialize_code feistelIn := (.block (ePart ++ kPart ++ maskPart) : Prog isa)
materialize_code feistelTree := (.block treePart : Prog isa)
materialize_code feistelOut := (.block pPart : Prog isa)

end VG.Impl.TripleDes.RISCV64
