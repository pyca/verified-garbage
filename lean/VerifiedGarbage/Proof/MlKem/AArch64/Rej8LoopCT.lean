module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8BodyCT

/-! # Relational timing of bounded mixed rejection -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem iters_relCT {w16 : Bool} {initial : List Zq} {N : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (ps : EnvW w16 N B bP aP s₀) (pu : EnvW w16 N B bP aP u₀)
    (hsp : s₀.sp=u₀.sp) (htab : s₀.gpr .x16=u₀.gpr .x16) (hN : 0<N) (hm : N%4=0) :
    RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ 0) (.loop (body w16) (.nonzero .x .x5))
      (fun s u => ResultW w16 initial N B aP s₀ s ∧ ResultW w16 initial N B aP u₀ u) := by
  let I := fun m s u => ∃t,m=N-t ∧ t<N ∧ t%4=0 ∧ PairInvW w16 initial N B bP aP s₀ u₀ t s u
  have step : ∀m,RelCT isa (I m) (body w16) (fun s u =>
      isa.eval (.nonzero .x .x5) s=isa.eval (.nonzero .x .x5) u ∧
      (isa.eval (.nonzero .x .x5) s=some false → ResultW w16 initial N B aP s₀ s ∧ ResultW w16 initial N B aP u₀ u) ∧
      (isa.eval (.nonzero .x .x5) s=some true → ∃m'<m,I m' s u)) := by
    intro m s u tr ur s' u' hp es eu
    obtain ⟨t,rfl,ht,htm,hp⟩ := hp
    have ht4 : t+4≤N := by omega
    obtain ⟨htr,hr⟩ := body_relCT ps pu hsp htab ht4 s u tr ur s' u' hp es eu
    refine ⟨htr,?_⟩
    rcases hr with hr|⟨rs,ru,xs,xu⟩
    · have hx := (inv_public hr.1 hr.2.1 hsp).2 .x5 (by simp)
      refine ⟨by rw [eval_nonzero,eval_nonzero,hx],?_,?_⟩
      · intro hz
        have hz' : N-(t+4)=0 := by
          rw [eval_nonzero,ne_zero_iff,hr.1.x5] at hz
          have hh := of_decide_eq_false (Option.some.inj hz)
          omega
        have he : t+4=N := by omega
        rw [he] at hr
        exact ⟨⟨hr.1.acc,hr.1.keep,hr.2.2.1⟩,⟨hr.2.1.acc,hr.2.1.keep,hr.2.2.2⟩⟩
      · intro hz
        have hz' : N-(t+4)≠0 := by
          rw [eval_nonzero,ne_zero_iff,hr.1.x5] at hz
          exact of_decide_eq_true (Option.some.inj hz)
        exact ⟨N-(t+4),by omega,t+4,rfl,by omega,by omega,hr⟩
    · refine ⟨by rw [eval_nonzero,eval_nonzero,xs,xu],fun _ => ⟨rs,ru⟩,?_⟩
      intro hz
      rw [eval_nonzero,xs] at hz
      contradiction
  exact RelCT.mono (RelCT.loop I step N)
    (fun _ _ h => ⟨0,by omega,hN,rfl,h⟩) (fun _ _ h => h)

end VG.Proof.MlKem.AArch64.Rej8
