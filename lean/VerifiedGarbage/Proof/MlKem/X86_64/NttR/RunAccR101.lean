module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunAccR100
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunAccR100
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-KEM on x86-64: the NTT on registers, the second half of pass B to an accumulator

The state after half 1 of pass B storing to the accumulator at `r10`, as a
literal, from that after half 0, and the check of its output
(`checkAcc_r10`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64.NttR

materialize_value stAccR101

theorem checkAcc_r10 : checkAcc passBsAccR10 .r10 = true :=
  checkAcc_of (p₀ := passBAccR100) (p₁ := passBAccR101)
    (show stAccR101.any outAccOk = true by rw [stAccR101.lit_eq]; lit_decide)

end VG.Proof.MlKem.X86_64.NttR
