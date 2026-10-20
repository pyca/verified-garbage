module

public import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.NextBlock
public import VerifiedGarbage.Impl.MlKem.AArch64.Paired
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SingleStep
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullInit
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.NextBlock
meta import VerifiedGarbage.Impl.MlKem.AArch64.Paired
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SingleStep
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullInit
meta import VerifiedGarbage.TCB.Axioms

/-! # Public-address timing for paired and singleton SHAKE128 generation -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Impl.MlKem.AArch64

theorem ct_eraseOff_eq {c d : Prog isa} (rs : List Reg)
    (he : Code.eraseOff c=d) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) d hc).isSome=true) :
    ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs rs)) c :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs rs) (fun _ _ _ _ h => h)
    (Taint.isSome_check_of_eraseOff he h)

theorem init_ct (sb ss a b k : Nat) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x28]))
    (.block (Impl.MlKem.AArch64.Paired.init sb ss a b k)) := by
  unfold Impl.MlKem.AArch64.Paired.init ptrTo
  split <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x28])
    (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem squeeze_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x20,.x21,.x22]))
    Impl.MlKem.AArch64.Paired.squeeze := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19,.x20,.x21,.x22])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem single_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x20,.x22]))
    (.loop singleBody (.nonzero .x .x22)) := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19,.x20,.x22])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem squeezeBlock_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x20,.x21]))
    (.seq (Impl.Sha3.AArch64.Neon.X2.call true .x19 .x19 1536)
      (.block (Impl.Sha3.AArch64.Neon.X2.squeeze 21 .x19 .x20 .x21))) := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19,.x20,.x21])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem fullInit_ct {sb ss a k : Nat} (hss : ss<4096) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x28]))
    (.block (Impl.MlKem.AArch64.Paired.fullInit sb ss a k)) := by
  rw [fullInit_eq hss]
  simp only [ptrTo,ite_eq_left hss]
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19,.x28])
    (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem start_ct (sb ss a b k : Nat) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x28]))
    (.seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a b k)) Impl.MlKem.AArch64.Paired.squeeze) := by
  by_cases hs : ss<4096
  · apply ct_eraseOff_eq [.x28]
      (d := Code.eraseOff (.seq (.block (Impl.MlKem.AArch64.Paired.init 0 0 0 0 1)) Impl.MlKem.AArch64.Paired.squeeze))
      (by simp only [Impl.MlKem.AArch64.Paired.init,ptrTo,ite_eq_left hs]; rfl)
    taint_decide
  · apply ct_eraseOff_eq [.x28]
      (d := Code.eraseOff (.seq (.block (Impl.MlKem.AArch64.Paired.init 0 4096 0 0 1)) Impl.MlKem.AArch64.Paired.squeeze))
      (by simp only [Impl.MlKem.AArch64.Paired.init,ptrTo,ite_eq_right hs]; rfl)
    taint_decide

theorem fullStart_ct {sb ss a k : Nat} (hss : ss<4096) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x28]))
    (.seq (.block (Impl.MlKem.AArch64.Paired.fullInit sb ss a k))
      (.loop singleBody (.nonzero .x .x22))) := by
  apply ct_eraseOff_eq [.x19,.x28]
    (d := Code.eraseOff (.seq (.block (Impl.MlKem.AArch64.Paired.fullInit 0 0 0 1))
      (.loop singleBody (.nonzero .x .x22))))
    (by rw [fullInit_eq hss,fullInit_eq (by decide : 0<4096)]; simp only [ptrTo,ite_eq_left hss]; rfl)
  taint_decide

theorem nextBlock_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19])) nextBlock := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlKem.AArch64.Paired
