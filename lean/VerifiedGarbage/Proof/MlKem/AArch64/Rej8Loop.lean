module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Body

/-! # Termination and exact semantics of the mixed rejection loop -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem iters_ok {w16 : Bool} {initial : List Zq} {N : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ s : State} (hp : EnvW w16 N B bP aP s₀) (hN : 0<N) (hm : N%4=0)
    (h : Scalar.InvW w16 initial N B bP aP s₀ 0 s) (hc : Constants s) :
    WP isa (.loop (body w16) (.nonzero .x .x5)) s (ResultW w16 initial N B aP s₀) := by
  refine WP.loop (M := isa)
    (fun m u => ∃t,m=N-t ∧ t<N ∧ t%4=0 ∧ Scalar.InvW w16 initial N B bP aP s₀ t u ∧ Constants u)
    ?_ N s ⟨0,by omega,hN,rfl,h,hc⟩
  rintro m u ⟨t,rfl,ht,htm,hi,hic⟩
  have ht4 : t+4≤N := by omega
  refine WP.mono (body_ok hp hi hic ht4) fun v hv => ?_
  rcases hv with ⟨hv,hvc⟩ | ⟨hv,hx5⟩
  · by_cases he : t+4=N
    · apply Or.inl
      refine ⟨?_,?_⟩
      · rw [eval_nonzero,ne_zero_iff,hv.x5,he,Nat.sub_self]
        rfl
      · rw [he] at hv
        exact ⟨hv.acc,hv.keep,hvc⟩
    · apply Or.inr
      refine ⟨?_,N-(t+4),by omega,t+4,rfl,by omega,by omega,hv,hvc⟩
      rw [eval_nonzero,ne_zero_iff,hv.x5]
      have hn : N-(t+4)≠0 := by omega
      exact congrArg some (decide_eq_true hn)
  · apply Or.inl
    refine ⟨?_,hv⟩
    rw [eval_nonzero,hx5]
    rfl

end VG.Proof.MlKem.AArch64.Rej8
