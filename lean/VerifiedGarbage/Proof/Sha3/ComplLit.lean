module

public import VerifiedGarbage.Proof.Sha3.Compl
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha3.Compl
meta import VerifiedGarbage.Proof.Framework.Lit

/-! # Keccak-f[1600] on complemented lanes: the round's polynomials as tables

The rounds of `X86_64/Round.lean`, `PPC64LE/Round.lean` and
`RISCV64/Round.lean` are checked against `Compl.specP`, which the kernel
evaluates there. `specP` reads the tables of `sD` and `sB`
(`materialize_table`, `Proof/Framework/Lit.lean`), so that the kernel
evaluates each of their values once, not once for each lane that uses it.

The tables are made here, once, rather than in each of those modules: a
table is a constant `c.lit` named after `c`, so two modules that each make
one cannot be imported together.
-/

@[expose] public section

namespace VG.Proof.Sha3.Compl

open VG.Bitslice.Anf

deriving instance Lean.ToExpr for Poly

materialize_table sD 5
materialize_table sB 5 5
materialize_table specP 25

end VG.Proof.Sha3.Compl
