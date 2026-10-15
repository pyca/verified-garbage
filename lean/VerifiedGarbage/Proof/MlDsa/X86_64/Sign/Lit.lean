module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
meta import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-DSA signing on x86-64: its code without the arithmetic, as literals

The signing function of each parameter set with every function of the
polynomial arithmetic empty (`primsWith .empty`), which the checks that it
never writes `rsp`, uses no stack, calls at most so deep and loads MXCSR only
to restore it evaluate (`sign0_sp`, `sign0_ctlC`, `sign0_noSp`,
`sign0_depth`), as literals (`materialize_code`, `Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG.X86_64

/-- Signing with ML-DSA-44, without the arithmetic. -/
def sign44 : Prog isa := Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) Spec.MlDsa.mlDsa44
/-- Signing with ML-DSA-65, without the arithmetic. -/
def sign65 : Prog isa := Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) Spec.MlDsa.mlDsa65
/-- Signing with ML-DSA-87, without the arithmetic. -/
def sign87 : Prog isa := Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) Spec.MlDsa.mlDsa87

materialize_code sign44
materialize_code sign65
materialize_code sign87

end VG.Proof.MlDsa.X86_64.Sign
