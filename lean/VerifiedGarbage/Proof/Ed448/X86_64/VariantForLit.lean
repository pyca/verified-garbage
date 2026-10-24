module

public import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
public import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit

/-!
# The variants' code as the registrations write it, as literals

The registrations generic over the field (`Generic/Curve448Field/X86_64/`)
write their code with the variant, `scalarBaseFor v` and `verifyEquationFor v`
(directly, or as a call of the function), which `lit_decide` (their `spSafe`,
by cases on `v`) does not rewrite to the literals of `scalarBase`,
`scalarBaseAdx`, `verifyEquation` and `verifyEquationAdx`: it would evaluate the
code again. A literal of code written as a term (`materialize_code N := t`,
`Proof/Framework/Lit.lean`) is found where the term occurs as written, so each
literal is given here again, as `N.lit` and `N.lit_eq : t = N.lit` for the
term `t` of each variant (by the constant's equation, the two being the same by
unfolding it), and nothing is evaluated again.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86_64

open VG.Impl.Ed448.X86_64

noncomputable def scalarBaseScalar.lit : Prog VG.X86_64.isa := scalarBase.lit
theorem scalarBaseScalar.lit_eq : scalarBaseFor .scalar = scalarBaseScalar.lit := scalarBase.lit_eq

noncomputable def scalarBaseAdxFor.lit : Prog VG.X86_64.isa := scalarBaseAdx.lit
theorem scalarBaseAdxFor.lit_eq : scalarBaseFor .adx = scalarBaseAdxFor.lit := scalarBaseAdx.lit_eq

noncomputable def verifyEquationScalar.lit : Prog VG.X86_64.isa := verifyEquation.lit
theorem verifyEquationScalar.lit_eq : verifyEquationFor .scalar = verifyEquationScalar.lit :=
  verifyEquation.lit_eq

noncomputable def verifyEquationAdxFor.lit : Prog VG.X86_64.isa := verifyEquationAdx.lit
theorem verifyEquationAdxFor.lit_eq : verifyEquationFor .adx = verifyEquationAdxFor.lit :=
  verifyEquationAdx.lit_eq

end VG.Proof.Ed448.X86_64
