module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeBasisCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeBasis

/-! Exactly four public basis rounds construct all thirty-two comb entries. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm

theorem tableLoop_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32} {start : Nat}
    (first : 0<start) (last : start<5) (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p))
    (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32) :
    RelCT isa (fun s t => BasisInput p sp start s ∧ BasisInput p sp start t ∧ s.sp=t.sp)
      (.loop (VG.Impl.Ffdh.Arm.CombPrecompute.basis
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) .ne) (fun _ _ => True) := by
  let I := fun k s t => ∃j, j+k=5 ∧ 0<k ∧ 0<j ∧
    BasisInput p sp j s ∧ BasisInput p sp j t ∧ s.sp=t.sp
  have step : ∀k, RelCT isa (I k) (VG.Impl.Ffdh.Arm.CombPrecompute.basis
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun u v => isa.eval .ne u=isa.eval .ne v ∧ (isa.eval .ne u=some false → True) ∧
        (isa.eval .ne u=some true → ∃m<k,I m u v)) := by
    intro k s t tr1 tr2 u v h e1 e2
    obtain ⟨j,parts,kpos,jpos,left,right,spEq⟩ := h
    have hj : j<5 := by omega
    obtain ⟨trace,sp'⟩ := relCT_keep_sp (basis_ct backend (p:=p) (sp:=sp) hj jpos positive fits)
      (fun _ _ h => h.2.2) s t tr1 tr2 u v ⟨left,right,spEq⟩ e1 e2
    obtain ⟨_,_,run1,core1,power1,table1,high1,z1,_,_,_⟩ := basis_ok backend s left.core hj jpos
      positive fits left.power left.table left.high
    obtain ⟨_,_,run2,core2,power2,table2,high2,z2,_,_,_⟩ := basis_ok backend t right.core hj jpos
      positive fits right.power right.table right.high
    obtain ⟨_,rfl⟩ := Exec.det e1 run1
    obtain ⟨_,rfl⟩ := Exec.det e2 run2
    refine ⟨trace,?_,fun _ => trivial,?_⟩
    · change some (!u.z)=some (!v.z)
      rw [z1,z2]
    · intro again
      have nz : j≠4 := by
        intro eq
        change some (!u.z)=some true at again
        simp only [z1,eq,decide_true,Bool.not_true,Option.some.injEq,Bool.false_eq_true] at again
      exact ⟨k-1,by omega,j+1,by omega,by omega,by omega,
        ⟨core1,by simpa only [Nat.add_sub_cancel] using power1,table1,high1⟩,
        ⟨core2,by simpa only [Nat.add_sub_cancel] using power2,table2,high2⟩,sp'⟩
  exact (RelCT.loop I step (5-start)).mono
    (fun _ _ h => ⟨start,by omega,by omega,first,h.1,h.2.1,h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm.CombBuilder
