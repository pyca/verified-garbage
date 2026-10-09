import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoopTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def WideReady (σ : State) (b p : Addr) (n d : Nat) (L : List VG.Spec.MlDsa.Zq) (s : State) : Prop :=
  ParseInv σ b p n L d s ∧ s.gpr .x17=16 ∧
    s.gpr .x16=(if 16≤(s.gpr .x4).toNat ∧ 16≤(s.gpr .x5).toNat then 16 else 0)

theorem widePhase_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => WideReady σ b p n d L s ∧ WideReady τ b p n d L t)
      (.ite (.zero .x .x16) (.block []) (.loop wideBody (.nonzero .x .x16)))
      (fun s t => ∃j,ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t ∧ j%4=d%4) := by
  apply RelCT.ite
  · intro s t hp
    have hr := hp.1.1.publicRegs hm hsp hp.2.1
    rw [eval_zero,eval_zero,hp.1.2.2,hp.2.2.2,hr.2 .x4 (by simp),hr.2 .x5 (by simp)]
  · exact RelCT.block_nil (fun _ _ hp => ⟨d,hp.1.1.1,hp.1.2.1,rfl⟩)
  · intro s t tr ur s' t' hp es et
    have hg := hp.1.1.2.2
    rw [hp.1.1.1.x4,hp.1.1.1.x5] at hg
    have hgood : 16≤256-(parsed σ b L d).length ∧ 16≤n-d := by
      by_contra hn
      have he := hp.2
      rw [eval_zero,hg,ite_eq_right hn] at he
      contradiction
    exact wideLoop_relCT hs ht hm hsp (by omega) (by omega) _ _ _ _ _ _
      ⟨hp.1.1.1,hp.1.2.1,hp.1.1.2.1,hp.1.2.2.1⟩ es et

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
