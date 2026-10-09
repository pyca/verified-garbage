import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.AddSub

namespace VG.Proof.MlDsa.AArch64.Optimized.AddSub
open VG VG.AArch64
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (accK acc_agree accSat)
open VG.Spec.MlDsa (polyAt)

private theorem correct (sub : Bool) (op : Spec.MlDsa.Poly → Spec.MlDsa.Poly → Spec.MlDsa.Poly)
    (hval : ∀ s, (accK op).pre s → ∀ i < 256,
      result sub (Spec.MlDsa.coeffAt s.mem (s.gpr .x0) i).toNat
        (Spec.MlDsa.coeffAt s.mem (s.gpr .x1) i).toNat =
        ((op (polyAt s.mem (s.gpr .x0)) (polyAt s.mem (s.gpr .x1)))[i]!).val)
    (s : State) (hp : (accK op).pre s) :
    ∃ tr t, Exec isa (VG.Impl.MlDsa.AArch64.Optimized.AddSub.code sub) s tr t ∧
      abiPreserved s t ∧ (accK op).post s t := by
  obtain ⟨tr,t,he,hi⟩ := run_ok sub s hp
  refine ⟨tr,t,he,VG.Proof.MlKem.AArch64.abi_of rfl ?_ he ?_,
    polyIs_of_toNat fun i hit => ?_⟩
  · cases sub <;> decide +kernel
  · cases sub <;> decide +kernel
  · have hlt : i < 256 := hit
    rw [hi.coeff i hlt,ite_eq_left (by omega)]
    exact hval s hp i hlt

theorem add_correct (s : State) (hp : (accK Spec.MlDsa.add).pre s) :
    ∃ tr t, Exec isa (VG.Impl.MlDsa.AArch64.Optimized.AddSub.code false) s tr t ∧
      abiPreserved s t ∧ (accK Spec.MlDsa.add).post s t := by
  apply correct false Spec.MlDsa.add ?_ s hp
  intro a ha i hi
  rw [add_get _ _ hi, val_add']
  simp only [result, Bool.false_eq_true, ↓reduceIte,polyAt_val ha.2.2.2.1 hi,
    polyAt_val ha.2.2.2.2 hi]

theorem sub_correct (s : State) (hp : (accK Spec.MlDsa.sub).pre s) :
    ∃ tr t, Exec isa (VG.Impl.MlDsa.AArch64.Optimized.AddSub.code true) s tr t ∧
      abiPreserved s t ∧ (accK Spec.MlDsa.sub).post s t := by
  apply correct true Spec.MlDsa.sub ?_ s hp
  intro a ha i hi
  rw [sub_get _ _ hi, val_sub,condSub_eq]
  · simp only [result, ↓reduceIte,polyAt_val ha.2.2.2.1 hi,polyAt_val ha.2.2.2.2 hi]
  · have := (polyAt a.mem (a.gpr .x0))[i]!.isLt
    have := (polyAt a.mem (a.gpr .x1))[i]!.isLt
    omega

theorem add_verified : Verified target (VG.Impl.MlDsa.AArch64.Optimized.AddSub.code false)
    (Spec.MlDsa.addContract abi) :=
  Verified.of_correct add_correct
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1]) acc_agree (by taint_decide))
    (by mldsa_implies [Spec.MlDsa.addContract,Spec.MlDsa.accSig,accK,abi,argRegs] [accSat] using accSat)

theorem sub_verified : Verified target (VG.Impl.MlDsa.AArch64.Optimized.AddSub.code true)
    (Spec.MlDsa.subContract abi) :=
  Verified.of_correct sub_correct
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1]) acc_agree (by taint_decide))
    (by mldsa_implies [Spec.MlDsa.subContract,Spec.MlDsa.accSig,accK,abi,argRegs] [accSat] using accSat)
end VG.Proof.MlDsa.AArch64.Optimized.AddSub
