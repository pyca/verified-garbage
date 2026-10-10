import VerifiedGarbage.Proof.Sha3.AArch64.Callers.Sums
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.KeyGen
import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.ExpandMask

/-!
# Constant time of ML-DSA's calls of the sponge, for any Keccak backend

Each check, once for any backend `c` with the summaries `sums c`
(`Callers/Sums.lean`, `taint_decide_generic`), for each backend's
`Permutation` (`Proof/Sha3/AArch64/Variant.lean`).
-/

namespace VG.Proof.Sha3.AArch64.Callers

open VG VG.AArch64

theorem mldsaNttTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
      (Impl.MlDsa.AArch64.Sample.spongeWith c 168 1008) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mldsaBoundedTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
      (Impl.MlDsa.AArch64.Sample.spongeWith c 136 544) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mldsaBallTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
      (Impl.MlDsa.AArch64.Sample.spongeWith c 136 272) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mldsaMaskTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
      (Impl.MlDsa.AArch64.Sample.expandMaskTailWith c) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mldsaSeedsTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
      (Impl.MlDsa.AArch64.KeyGen.shake256With c [⟨.x25, 0, 32⟩, ⟨.x28, 896, 2⟩] [⟨.x28, 1024, 128⟩]) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mldsaTrHashTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∀ p : Spec.MlDsa.Params,
      (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
      (Impl.MlDsa.AArch64.KeyGen.trHashWith c p) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;>
    taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mldsaVerifyHashTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∀ p : Spec.MlDsa.Params,
      (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
      (Impl.MlDsa.AArch64.KeyGen.shake256With c [⟨.x26, 0, 64⟩,
        ⟨.x28, (Impl.MlDsa.AArch64.Verify.bP p).2, p.k * Impl.MlDsa.AArch64.Verify.w1Len p⟩]
        [⟨.x28, 1024, p.ctildeLen⟩]) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;>
    taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mldsaSignDecodeTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
      (Impl.MlDsa.AArch64.Sign.shakeAtWith c [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, 960, 64⟩) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mldsaSignCommitTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∀ p : Spec.MlDsa.Params,
      (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
      (Impl.MlDsa.AArch64.Sign.shakeAtWith c [⟨.x26, 0, 64⟩,
        ⟨.x28, 2048, p.k * Impl.MlDsa.AArch64.Sign.w1Len p⟩]
        ⟨.x28, 1040, Impl.MlDsa.AArch64.Sign.cLen p⟩) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;>
    taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

end VG.Proof.Sha3.AArch64.Callers
