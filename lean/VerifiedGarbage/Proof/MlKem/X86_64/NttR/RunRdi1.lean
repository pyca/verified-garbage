module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunRdi0
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunRdi0
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-KEM on x86-64: the NTT on registers, the second half of pass B to `rdi`

The state after half 1 of pass B storing to `rdi`, as a literal, from that
after half 0, and the check of its output (`check_rdi`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64.NttR

materialize_value stRdi1

theorem check_rdi : check passBsRdi .rdi = true :=
  check_of (p₀ := passBRdi0) (p₁ := passBRdi1) (show stRdi1.any outOk = true by rw [stRdi1.lit_eq]; lit_decide)

end VG.Proof.MlKem.X86_64.NttR
