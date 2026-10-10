import VerifiedGarbage.Proof.Sha3.AArch64.Callers.Sums
import VerifiedGarbage.Impl.MlKem1024.AArch64.Encaps
import VerifiedGarbage.Impl.MlKem1024.AArch64.Decaps
import VerifiedGarbage.Impl.MlKem.AArch64.Encaps
import VerifiedGarbage.Impl.MlKem.AArch64.Decaps
import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen
import VerifiedGarbage.Impl.MlKem.AArch64.Sample

/-!
# Constant time of ML-KEM's calls of the sponge, for any Keccak backend

Each check, once for any backend `c` with the summaries `sums c`
(`Callers/Sums.lean`, `taint_decide_generic`), for each backend's
`Permutation` (`Proof/Sha3/AArch64/Variant.lean`).
-/

namespace VG.Proof.Sha3.AArch64.Callers

open VG VG.AArch64

theorem sampleFullTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2])
      (Impl.MlKem.AArch64.sampleSqueezeWith c) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem sampleFastTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2])
      (Impl.MlKem.AArch64.sampleSqueezeNWith c 504 (Impl.MlKem.AArch64.sampleRegs 168)) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mlkemKgATaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
      (Impl.MlKem.AArch64.kgAWith c) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mlkemKgCTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
      (Impl.MlKem.AArch64.kgCWith c) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mlkemEnATaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (Impl.MlKem.AArch64.enAWith c) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mlkemEnCTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
      (Impl.MlKem.AArch64.enCWith c) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mlkemDeATaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
      (Impl.MlKem.AArch64.deAWith c) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mlkemDeCTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
      (Impl.MlKem.AArch64.deCWith c) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mlkem1024KgATaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
      (Impl.MlKem1024.AArch64.kgAWith c) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mlkem1024KgCTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
      (Impl.MlKem1024.AArch64.kgCWith c) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mlkem1024EnATaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (Impl.MlKem1024.AArch64.enAWith c) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mlkem1024EnCTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
      (Impl.MlKem1024.AArch64.enCWith c) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mlkem1024DeATaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
      (Impl.MlKem1024.AArch64.deAWith c) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

theorem mlkem1024DeCTaint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (sums c)) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
      (Impl.MlKem1024.AArch64.deCWith c) h).isSome = true := by
  taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

end VG.Proof.Sha3.AArch64.Callers
