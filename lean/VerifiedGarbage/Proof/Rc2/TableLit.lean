module

public import VerifiedGarbage.Proof.Rc2.Table
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Rc2.Table
meta import VerifiedGarbage.Proof.Framework.Lit
-- separate module: the literal of a table that only code carrying it in its instructions evaluates

/-!
# RC2: PITABLE's table of constants as a literal

`Impl.Rc2.piQuads` as a literal, for the code whose instructions carry the
table: read from PITABLE's packed table (`Rc2.piTable_getD`), as the
quadwords' bytes are (`Proof.Rc2.piQuadNat`), rather than from the
specification's vector.
-/

@[expose] public section

namespace VG.Impl.Rc2

/-- `piQuads`, reading PITABLE from its packed table. -/
def piQuadsLit : List (BitVec 64) := (List.range 32).map Proof.Rc2.piQuadNat

materialize_value piQuadsLit

/-- `piQuads`'s literal: the one of `piQuadsLit`. -/
noncomputable abbrev piQuads.lit : List (BitVec 64) := piQuadsLit.lit

theorem piQuads.lit_eq : piQuads = piQuads.lit :=
  Eq.trans (b := piQuadsLit) (by rw [piQuads, piQuadsLit, Proof.Rc2.piQuad_eq]) piQuadsLit.lit_eq

end VG.Impl.Rc2
