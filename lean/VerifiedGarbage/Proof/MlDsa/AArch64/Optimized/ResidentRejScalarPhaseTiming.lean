import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase
import VerifiedGarbage.Proof.Framework.AArch64.Exec

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def ScalarReady (σ : State) (b p : Addr) (n d : Nat) (L : List VG.Spec.MlDsa.Zq) (s : State) : Prop :=
  ParseInv σ b p n L d s ∧ s.gpr .x16=s.gpr .x4*s.gpr .x5

theorem scalarBranch_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ScalarReady σ b p n d L s ∧ ScalarReady τ b p n d L t)
      (.ite (.zero .x .x16) (.block []) scalarLoop) (fun _ _ => True) := by
  apply RelCT.ite
  · intro s t hp
    have hr := hp.1.1.publicRegs hm hsp hp.2.1
    rw [eval_zero,eval_zero,hp.1.2,hp.2.2,hr.2 .x4 (by simp),hr.2 .x5 (by simp)]
  · exact RelCT.block_nil (fun _ _ _ => trivial)
  · intro s t tr ur s' t' hp es et
    have hnonzero : s.gpr .x16≠0#64 := by
      intro hz
      have hh := hp.2
      rw [eval_zero,hz] at hh
      contradiction
    have h4 : (s.gpr .x4).toNat≠0 := by
      intro hz
      apply hnonzero
      rw [hp.1.1.2,show s.gpr .x4=0#64 from BitVec.eq_of_toNat_eq hz,BitVec.zero_mul]
    have h5 : (s.gpr .x5).toNat≠0 := by
      intro hz
      apply hnonzero
      rw [hp.1.1.2,show s.gpr .x5=0#64 from BitVec.eq_of_toNat_eq hz,BitVec.mul_zero]
    rw [hp.1.1.1.x4] at h4
    rw [hp.1.1.1.x5] at h5
    have hb := hp.1.1.1.bound
    exact scalarLoop_relCT hs ht hm hsp (by omega) (by omega) _ _ _ _ _ _ ⟨hp.1.1.1,hp.1.2.1⟩ es et

private theorem scalarSetup_ok {σ s : State} {b p : Addr} {n d : Nat} {L : List VG.Spec.MlDsa.Zq}
    (h : ParseInv σ b p n L d s) :
    WP isa (.block [.mul .x .x16 .x4 .x5]) s (ScalarReady σ b p n d L) := by
  have hw : WP isa (.block [.mul .x .x16 .x4 .x5]) s fun t =>
      Only [.x16] s t ∧ t.gpr .x16=s.gpr .x4*s.gpr .x5 :=
    wp_mul fun t ht et => wp_nil ⟨ht,et⟩
  refine WP.mono (WP.keepV (by decide) hw) fun t ⟨⟨ht,hg⟩,hv⟩ => ?_
  exact ⟨h.of_control (ht.mono (by decide)) hv,by rw [ht.get .x4,ht.get .x5]; exact hg⟩

theorem scalarPhase_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.seq (.block [.mul .x .x16 .x4 .x5])
        (.ite (.zero .x .x16) (.block []) scalarLoop)) (fun _ _ => True) := by
  apply RelCT.seq (R := fun s t => ScalarReady σ b p n d L s ∧ ScalarReady τ b p n d L t)
  · intro s t tr ur s' t' hp es et
    have hg := hp.1.publicRegs hm hsp hp.2
    have hct : RelCT isa (fun s t => s.sp=t.sp)
        (.block [.mul .x .x16 .x4 .x5]) (fun _ _ => True) :=
      RelCT.taint (A := taint) (Taint.ofRegs [])
        (fun _ _ h => ⟨h,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) (by taint_decide)
    obtain ⟨_,a,ea,ha⟩ := scalarSetup_ok hp.1
    obtain ⟨_,b,eb,hb⟩ := scalarSetup_ok hp.2
    obtain ⟨_,rfl⟩ := Exec.det es ea
    obtain ⟨_,rfl⟩ := Exec.det et eb
    exact ⟨(hct _ _ _ _ _ _ hg.1 es et).1,ha,hb⟩
  · exact scalarBranch_relCT hs ht hm hsp

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
