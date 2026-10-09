import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourLoopTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def FourReady (σ : State) (b p : Addr) (n d : Nat) (L : List VG.Spec.MlDsa.Zq) (s : State) : Prop :=
  ParseInv σ b p n L d s ∧ s.gpr .x17=4 ∧
    s.gpr .x16=(if 4≤(s.gpr .x4).toNat then s.gpr .x5 else 0)

theorem fourPhase_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hmod : d%4=n%4) :
    RelCT isa (fun s t => FourReady σ b p n d L s ∧ FourReady τ b p n d L t)
      (.ite (.zero .x .x16) (.block []) (.loop vectorBody (.nonzero .x .x16)))
      (fun s t => ∃j,ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t  ) := by
  apply RelCT.ite
  · intro s t hp
    have hr := hp.1.1.publicRegs hm hsp hp.2.1
    rw [eval_zero,eval_zero,hp.1.2.2,hp.2.2.2,hr.2 .x4 (by simp),hr.2 .x5 (by simp)]
  · exact RelCT.block_nil (fun _ _ hp => ⟨d,hp.1.1.1,hp.1.2.1⟩)
  · intro s t tr ur s' t' hp es et
    have hg := hp.1.1.2.2
    rw [hp.1.1.1.x4] at hg
    have hcap : 4≤256-(parsed σ b L d).length := by
      by_contra hn
      have he := hp.2
      rw [eval_zero,hg,ite_eq_right hn] at he
      contradiction
    have hcount : n-d≠0 := by
      intro hn
      have hx : s.gpr .x5=0#64 := BitVec.eq_of_toNat_eq (hp.1.1.1.x5.trans hn)
      have he := hp.2
      rw [eval_zero,hg,ite_eq_left hcap,hx] at he
      contradiction
    have hb := hp.1.1.1.bound
    exact fourLoop_relCT hs ht hm hsp (by omega) hmod (by omega) _ _ _ _ _ _
      ⟨hp.1.1.1,hp.1.2.1,hp.1.1.2.1,hp.1.2.2.1⟩ es et

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
