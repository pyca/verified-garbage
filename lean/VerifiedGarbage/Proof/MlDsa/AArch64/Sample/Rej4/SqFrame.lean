import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqPhase

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf oX2)

theorem pair_frame {σ : State} {p n i : Nat} (hp : p < 2) (hn : n < 6) (hi : i < 2) (hip : i ≠ p)
    {m m' : Mem} (hf : Frame (blockW σ p n) m m')
    {A B : Spec.Sha3.State} (hpair : PairAt m (stateP σ i) A B) : PairAt m' (stateP σ i) A B := by
  intro j hj
  rw [hf.read (pair_contains (stateP σ i) hj) (fun r hr => ?_) (by decide)]
  · exact hpair j hj
  simp only [blockW,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint (scr σ) (d := 400*i) (n := 400) (e := 400*p) (k := 400)
      (by omega) (by omega) (by omega)
  · exact Offset.disjoint (scr σ) (d := 400*i) (n := 400) (e := oBuf+1008*(2*p)+168*n) (k := 168)
      (by dsimp only [oBuf]; omega) (by omega) (by dsimp only [oBuf]; omega)
  · exact Offset.disjoint (scr σ) (d := 400*i) (n := 400) (e := oBuf+1008*(2*p+1)+168*n) (k := 168)
      (by dsimp only [oBuf]; omega) (by omega) (by dsimp only [oBuf]; omega)
  · exact Offset.disjoint (scr σ) (d := 400*i) (n := 400) (e := oX2) (k := 136)
      (by dsimp only [oX2]; omega) (by omega) (by decide)

theorem b_regs : ∀ k < 4,bReg k ∉ blockRegs := by decide
end VG.Proof.MlDsa.AArch64.Sample.Rej4
