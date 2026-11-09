module

import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopTiming
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedRest
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Correct
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsForget
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitializationTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSignTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedExpansion
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTrace
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopTiming
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedRest
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Correct
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsForget
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitializationTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSignTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedExpansion
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTrace
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.TCB.Axioms

/-! ## From `OptimizedPairedRestTiming.lean` -/

@[expose] public section

/-! ## From `OptimizedPairedSignTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : Proof.Sha3.AArch64.Permutation}

def WithPaired (S : Nat) (R : State → State → Prop) (x y : State) : Prop :=
  R x y ∧ PairedRoots S x ∧ PairedRoots S y ∧
    x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR"

theorem withPaired_tr {S : Nat} {R Q : State → State → Prop} {code : Prog isa}
    (hd : 16*code.aarch64Depth≤S) (hS : S<2^64) (ht : RelCT isa R code Q) :
    RelCT isa (WithPaired S R) code (WithPaired S Q) := by
  intro x y tx ty x' y' h ex ey
  have res := ht _ _ _ _ _ _ h.1 ex ey
  exact ⟨res.1,res.2,h.2.1.exec ex hd hS,h.2.2.1.exec ey hd hS,by
    simpa only [VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using h.2.2.2⟩

end VG.Proof.MlDsa.AArch64.Sign

end
