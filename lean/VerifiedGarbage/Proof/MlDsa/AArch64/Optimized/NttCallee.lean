import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

/-- The expanded-root NTT needs no stack. Its immutable table remains part of
its callee contract rather than being silently added to the caller's memory. -/
theorem positiveNtt_callee (S : Nat) :
    CalleeOk S staticNtt (positiveNttContract (abi.withConsts nttConsts)) := by
  refine ⟨positiveNtt_verified.1,positiveNtt_verified.2.1,?_⟩
  change 0≤S
  exact Nat.zero_le _

/-- The separate-source entry has the same zero-stack, table-aware boundary. -/
theorem positiveNttOut_callee (S : Nat) :
    CalleeOk S outNtt (positiveNttOutContract (abi.withConsts nttConsts)) := by
  refine ⟨positiveNttOut_verified.1,positiveNttOut_verified.2.1,?_⟩
  change 0≤S
  exact Nat.zero_le _

end VG.Proof.MlDsa.AArch64.Optimized
