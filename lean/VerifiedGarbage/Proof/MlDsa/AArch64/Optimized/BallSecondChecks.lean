import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSecondPrefix
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Backend

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3

def PrefixTiming (c : Impl.Sha3.AArch64.Callee) : Prop :=
  RelCT isa (VectorTaint.Agree (VectorTaint.ofRegs [.x0,.x25])) (secondPrefix c) (fun _ _ => True)

 theorem sha3_prefixTiming : PrefixTiming callee := by
  have hh : ∃hint, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x25]) (secondPrefix callee) hint).isSome=true := by sponge_taint_decide Sha3Sums
  obtain ⟨hint,hh⟩ := hh
  exact RelCT.taint (A := VectorTaint.taint) _ (fun _ _ h => h) hh
end VG.Proof.MlDsa.AArch64.Optimized.Ball
