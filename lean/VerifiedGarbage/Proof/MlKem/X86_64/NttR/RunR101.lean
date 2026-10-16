module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunR100
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunR100
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-KEM on x86-64: the NTT on registers, the second half of pass B to `r10`

The state after half 1 of pass B storing to `r10`, as a literal, from that
after half 0, and the check of its output (`check_r10`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64.NttR

materialize_value stR101

theorem check_r10 : check passBsR10 .r10 = true :=
  check_of (p₀ := passBR100) (p₁ := passBR101) (show stR101.any outOk = true by rw [stR101.lit_eq]; lit_decide)

end VG.Proof.MlKem.X86_64.NttR
