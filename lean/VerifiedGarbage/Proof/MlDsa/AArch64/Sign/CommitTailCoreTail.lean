import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailCoreFull

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

theorem coreTail65_ok {σ s : State} {w1 work : Addr} {A B : Spec.Sha3.State}
    (hc : CoreConfig σ 768 w1 work) (h : RoundState σ 768 w1 work A B 5 6 s) :
    WP isa (.block tail) s (CoreState σ 768 w1 work A B 6) := by
  have hptr : s.gpr .x5=w1+BitVec.ofNat 64 752 := h.ptr
  refine WP.mono (tail_ok h.pairs (fun j hj=>?_)) fun t ⟨hk,hm,hp⟩ => ?_
  · rw [hptr,Offset.add_add]
    exact h.toCoreEnv.readable hc (by omega)
  · have he : xorWords (Spec.Sha3.keccakF (lowRun 768 σ.mem w1 A 5)) s.mem
        (w1+BitVec.ofNat 64 752) 2 =
      xorWords (Spec.Sha3.keccakF (lowRun 768 σ.mem w1 A 5)) σ.mem
        (w1+BitVec.ofNat 64 752) 2 := by
      apply xorWords_congr
      intro j hj
      rw [Offset.add_add]
      exact h.toCoreEnv.word hc (by omega)
    rw [hptr,he] at hp
    refine ⟨⟨(h.keep.trans hk).mono (by simp [coreRegs]),?_,?_,?_⟩,?_⟩
    · rw [hm]; exact h.frame
    · rw [hk.gpr .x5 (by decide)]
      exact h.ptr
    · rw [hm]; exact h.output
    · change Pairs t (absorbAfter 768 σ.mem w1 5 (Spec.Sha3.keccakF (lowRun 768 σ.mem w1 A 5))) _
      simpa only [absorbAfter,Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceLT,
        Nat.reduceMul,ite_false,ite_true] using hp

theorem coreTail87_ok {σ s : State} {w1 work : Addr} {A B : Spec.Sha3.State}
    (h : RoundState σ 1024 w1 work A B 7 8 s) :
    WP isa (.block (paddingWord 0 31 0 ++ paddingWord 16 0x8000 3)) s
      (CoreState σ 1024 w1 work A B 8) := by
  refine WP.mono (padding_ok (by decide) h.pairs) fun t ⟨hk,hm,hp⟩ => ?_
  refine ⟨⟨(h.keep.trans hk).mono (by simp [coreRegs]),?_,?_,?_⟩,?_⟩
  · rw [hm]; exact h.frame
  · rw [hk.gpr .x5 (by decide)]
    exact h.ptr
  · rw [hm]; exact h.output
  · change Pairs t (absorbAfter 1024 σ.mem w1 7 (Spec.Sha3.keccakF (lowRun 1024 σ.mem w1 A 7))) _
    simpa only [absorbAfter,Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceLT,
      ite_false,ite_true,ite_eq_right (by decide : ¬ (1024:Nat)=768)] using hp

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
