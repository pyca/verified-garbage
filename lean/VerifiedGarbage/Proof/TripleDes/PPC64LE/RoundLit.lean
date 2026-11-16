module

public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block
public import VerifiedGarbage.Proof.Framework.Bitslice.PosTable
public import VerifiedGarbage.Proof.Framework.Bitslice.Table
public import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.SboxTables
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block
meta import VerifiedGarbage.Proof.Framework.Bitslice.PosTable
meta import VerifiedGarbage.Proof.Framework.Bitslice.Table
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-!
The round function's words of constants, its lanes' tables (each lane's
table in its block of 64 bits, `Bitslice.blocks`) and its three parts, as
literals.
-/

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE

open VG.PPC64LE

/-- The tables of the 64 lanes, each in its block of 64 bits. -/
def laneTables : Nat := VG.Bitslice.blocks 64 (fun p => VG.Bitslice.tableOf (laneBit p) 64) 64

/-- `laneBit`, its S-box's output read from the truth tables of
`Proof/TripleDes/SboxTables.lean`, which the kernel has evaluated once for
every target: the literals below hold 2048 values of `laneBit` in the
leaves and as many in the lanes' tables, and read them (`unfoldToLits`
rewrites `laneBit` to this, as to a table of `materialize_table`) rather
than evaluate the specification's S-boxes again. -/
noncomputable abbrev laneBit.lit (p x : Nat) : Bool :=
  x / 32 == p % 8 / 4 &&
    (Proof.TripleDes.outputTable.lit (7 - p / 8) (laneOut (p / 8) (p % 8))).testBit x

theorem laneBit.lit_eq : laneBit = laneBit.lit := by
  funext p x
  rw [laneBit, laneBit.lit, ← Proof.TripleDes.outputTable.lit_eq]
  by_cases hx : x < 64
  · rw [Proof.TripleDes.testBit_outputTable hx]
  · have h : (x / 32 == p % 8 / 4) = false := by
      rw [beq_eq_false_iff_ne]; omega
    rw [h, Bool.false_and, Bool.false_and]

-- P's moves and their distances, a search that the words of constants
-- (`pLarge`) and P's code both run.
materialize_value pMoves
materialize_value pDistances

materialize_value roundConsts
materialize_value laneTables

materialize_code feistelIn := (.block (ePart ++ kPart ++ maskPart) : Prog isa)
materialize_code feistelTree := (.block treePart : Prog isa)
materialize_code feistelOut := (.block pPart : Prog isa)

end VG.Impl.TripleDes.PPC64LE
