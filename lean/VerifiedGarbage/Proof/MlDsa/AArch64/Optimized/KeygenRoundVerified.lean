import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundSemantic

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Round (power2RoundK p2rSat)
open VG.Proof.MlDsa.Round (natPolyIs_of_toNat map_get)
open VG.Proof.MlDsa.AArch64.Arith (pR)

theorem correct (s : State) (hp : power2RoundK.pre s) :
    ∃tr t, Exec isa VG.Impl.MlDsa.AArch64.Optimized.KeygenRound.power2Round s tr t ∧
      abiPreserved s t ∧ power2RoundK.post s t := by
  obtain ⟨tr,t,he,hm⟩ := run_ok s (fun off ho =>
    ⟨pR (s.gpr .x0),by rw [hp.1]; simp,Offset.contains_base _ ho (by omega)⟩)
    (fun off ho => ⟨pR (s.gpr .x1),by rw [hp.2.1]; simp,Offset.contains_base _ ho (by omega)⟩)
    (fun off ho => ⟨pR (s.gpr .x2),by rw [hp.2.1]; simp,Offset.contains_base _ ho (by omega)⟩)
  have hfield := roundRun_prefix s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
    hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 (by decide : 64≤64)
  have hr := hp.2.2.2.2.2
  refine ⟨tr,t,he,VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he,?_,?_⟩
  · refine natPolyIs_of_toNat fun k hk => ?_
    rw [hm,(hfield k hk).1,ite_eq_left (by omega),highWord_eq (hr k hk),map_get _ _ hk,
      Round.t1V_toNat (hr k hk),VG.Proof.MlDsa.Round.power2Round_eq,←polyAt_val hr hk]
    exact (Int.toNat_natCast _).symm
  · refine polyIs_of_toNat fun k hk => ?_
    rw [hm,(hfield k hk).2,ite_eq_left (by omega),lowWord_eq (hr k hk),map_get _ _ hk,
      Round.t0V_toNat (hr k hk),VG.Proof.MlDsa.Round.power2Round_t0,polyAt_val hr hk]

theorem constantTime : ConstantTime isa power2RoundK.pre power2RoundK.pub
    VG.Impl.MlDsa.AArch64.Optimized.KeygenRound.power2Round :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x1,.x2])
    (fun _ _ _ _ hp => VG.Proof.MlDsa.AArch64.Arith.agree_regs hp.2.2.2 fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      exacts [hp.1,hp.2.1,hp.2.2.1]) (by taint_decide)

theorem power2Round_verified : Verified target
    VG.Impl.MlDsa.AArch64.Optimized.KeygenRound.power2Round (power2RoundContract abi) :=
  Verified.of_correct correct constantTime (by
    mldsa_implies [power2RoundContract,power2RoundSig,power2RoundK,abi,argRegs] [p2rSat] using p2rSat)

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
