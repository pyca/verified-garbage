import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailCoreRound

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

/-- Only the first five permutations serialize the independent mask stream. -/
theorem coreEmit_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work)
    (h : RoundState σ wlen w1 work A B i i s) :
    WP isa (.block (if i<5 then squeeze i else [])) s
      (RoundState σ wlen w1 work A B i (i+1)) := by
  by_cases hi : i<5
  · rw [ite_eq_left hi]
    have hw : s.gpr .x19=work := (h.keep.gpr .x19 (by decide)).trans hc.workPtr
    refine WP.mono (squeeze_ok i hi h.pairs ?_ ?_) fun t ⟨hk,hp,ho,hf⟩ => ?_
    · intro j hj
      rw [h.keep.wr,hw,Offset.add_add]
      exact hc.writable _ _ (by omega)
    · rw [h.keep.wr,hw]
      change InRegions σ.wr ((work+BitVec.ofNat 64 (256+136*i))+BitVec.ofNat 64 128) 8
      rw [Offset.add_add]
      exact hc.writable _ _ (by omega)
    · rw [hw,buffer_addr] at ho hf
      refine ⟨⟨(h.keep.trans hk).mono (by simp [coreRegs]),?_,?_,?_⟩,hp⟩
      · apply h.frame.trans
        exact hf.sub (by
          intro r hr
          rcases List.mem_singleton.mp hr with rfl
          exact ⟨bufferRegion work,by simp,Offset.sub_base (bufferBase work)
            (d:=136*i) (n:=136) (k:=680) (by omega)⟩)
      · rw [hk.gpr .x5 (by decide)]; exact h.ptr
      · rw [Nat.min_eq_left (by omega)]
        have hold := h.output
        rw [Nat.min_eq_left (by omega)] at hold
        exact streamOutput_append hi hold ho hf
  · rw [ite_eq_right hi]
    refine WP.block_nil_iff.mpr ⟨⟨h.keep,h.frame,h.ptr,?_⟩,h.pairs⟩
    have ho := h.output
    rw [Nat.min_eq_right (by omega)] at ho
    rw [Nat.min_eq_right (by omega)]
    exact ho

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
