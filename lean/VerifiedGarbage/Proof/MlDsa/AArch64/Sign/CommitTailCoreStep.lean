import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailCoreTail

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (rounds)

def absorbCode (wlen i : Nat) : List Instr :=
  let n := (64+wlen)/136
  if i<n-1 then full else if i==n-1 then
    if wlen=768 then tail else paddingWord 0 31 0 ++ paddingWord 16 0x8000 3
  else []

theorem coreAbsorb_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work)
    (h : RoundState σ wlen w1 work A B i (i+1) s) :
    WP isa (.block (absorbCode wlen i)) s (CoreState σ wlen w1 work A B (i+1)) := by
  by_cases hi : i<(64+wlen)/136-1
  · rw [absorbCode,ite_eq_left hi]
    exact coreFull_ok hc hi h
  · by_cases he : i=(64+wlen)/136-1
    · rcases hc.length with hw|hw
      · subst wlen
        have hi5 : i=5 := he
        subst i
        exact coreTail65_ok hc h
      · subst wlen
        have hi7 : i=7 := he
        subst i
        exact coreTail87_ok h
    · have hb : (i==((64+wlen)/136-1))=false := by simp [he]
      rw [absorbCode,ite_eq_right hi,hb]
      refine WP.block_nil_iff.mpr ⟨⟨h.keep,h.frame,?_,h.output⟩,?_⟩
      · rw [h.ptr,inputPtr,inputPtr,fullCount,fullCount,
          Nat.min_eq_right (by omega),Nat.min_eq_right (by omega)]
      · change Pairs s (absorbAfter wlen σ.mem w1 i
          (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i))) _
        rw [absorbAfter,ite_eq_right hi,ite_eq_right he]
        exact h.pairs

/-- One exact unrolled core step: shared permutation, optional mask squeeze,
and the next commitment absorb. -/
theorem coreStep_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work)
    (h : CoreState σ wlen w1 work A B i s) :
    WP isa (.seq (.block rounds)
      (.block ((if i<5 then squeeze i else []) ++ absorbCode wlen i))) s
      (CoreState σ wlen w1 work A B (i+1)) := by
  rw [WP.seq_iff]
  refine WP.mono (coreRound_ok h) fun a ha=>?_
  rw [WP.block_append_iff]
  exact WP.mono (coreEmit_ok hc ha) fun b hb=>coreAbsorb_ok hc hb

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
