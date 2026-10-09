import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRoundCall

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call

theorem p2rAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.power2Round (power2RoundContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {t t1 t0 : Ptr} (hc : p2rChk rbs wbs t t1 t0 = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ Reduced x.mem (pa x t) ∧ Reduced y.mem (pa y t) ∧
      SameB x y) :
    RelCT isa Q (Impl.MlDsa.AArch64.KeyGen.Optimized.power2RoundAt P t t1 t0) fun _ _ => True := by
  have hc' := hc
  simp only [p2rChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : t.1 ∈ bases ∧ t1.1 ∈ bases ∧ t0.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_tr C (p2r_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, p2r_pre Lx hc rx h1, ?_, ?_, (p2r_cov Lx hc).1, (p2r_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact p2r_pre Ly hc ry h2
  · sig_pub [power2RoundContract, power2RoundSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (p2r_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (p2r_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
