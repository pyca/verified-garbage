module

public import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
meta import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
public import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit

/-! Literal code for the ADX scalar multiplication and verification equation. -/

@[expose] public section

namespace VG

materialize_code Impl.Ed448.X86_64.scalarBaseAdx
materialize_code Impl.Ed448.X86_64.verifyEquationAdx

end VG
