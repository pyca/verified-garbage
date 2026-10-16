module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRun
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRun
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-KEM on x86-64: `NTT⁻¹` on registers, the first half of pass B from an accumulator

The state after half 0 of pass B reading an accumulator, for the functions that inline `NTT⁻¹`, as a literal.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64.NttR

materialize_value stIAcc0

end VG.Proof.MlKem.X86_64.NttR
