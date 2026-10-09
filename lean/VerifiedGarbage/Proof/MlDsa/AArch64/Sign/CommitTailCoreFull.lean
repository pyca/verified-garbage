import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailCoreEmit

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

private theorem full_bound {σ : State} {wlen i j : Nat} {w1 work : Addr}
    (hc : CoreConfig σ wlen w1 work) (hi : i<(64+wlen)/136-1) (hj : j<17) :
    72+136*i+8*j+8≤wlen := by
  rcases hc.length with he|he
  · rw [he] at hi ⊢
    simp only [Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub] at hi
    omega
  · rw [he] at hi ⊢
    simp only [Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub] at hi
    omega

/-- The next full commitment block is read from the immutable packed input. -/
theorem coreFull_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work)
    (hi : i<(64+wlen)/136-1) (h : RoundState σ wlen w1 work A B i (i+1) s) :
    WP isa (.block full) s (CoreState σ wlen w1 work A B (i+1)) := by
  have hptr : s.gpr .x5=w1+BitVec.ofNat 64 (72+136*i) := by
    rw [h.ptr,inputPtr,fullCount,Nat.min_eq_left (by omega)]
  refine WP.mono (full_ok h.pairs (fun j hj=>?_)) fun t ⟨hk,hm,hp5,hp⟩ => ?_
  · rw [hptr,Offset.add_add]
    exact h.toCoreEnv.readable hc (full_bound hc hi hj)
  · have he : xorWords (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i)) s.mem
        (w1+BitVec.ofNat 64 (72+136*i)) 17 =
      xorWords (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i)) σ.mem
        (w1+BitVec.ofNat 64 (72+136*i)) 17 := by
      apply xorWords_congr
      intro j hj
      rw [Offset.add_add]
      exact h.toCoreEnv.word hc (full_bound hc hi hj)
    rw [hptr,he] at hp
    refine ⟨⟨(h.keep.trans hk).mono (by simp [coreRegs]),?_,?_,?_⟩,?_⟩
    · rw [hm]; exact h.frame
    · rw [hp5,hptr]
      change (w1+BitVec.ofNat 64 (72+136*i))+BitVec.ofNat 64 136=inputPtr wlen w1 (i+1)
      rw [Offset.add_add,inputPtr,fullCount,Nat.min_eq_left (by omega)]
      congr 1
    · rw [hm]; exact h.output
    · change Pairs t (absorbAfter wlen σ.mem w1 i (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i))) _
      rw [absorbAfter,ite_eq_left hi]
      exact hp

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
