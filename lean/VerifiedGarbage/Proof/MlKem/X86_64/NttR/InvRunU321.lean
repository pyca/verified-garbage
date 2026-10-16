module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunU320
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunU320
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-KEM on x86-64: `NTT⁻¹` on registers, the second half of pass B from `u32`s

The state after half 1 of pass B, as a literal, from that after half 0.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64.NttR

materialize_value stIU321

end VG.Proof.MlKem.X86_64.NttR
