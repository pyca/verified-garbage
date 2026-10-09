import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailCoreStep

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (rounds)

def coreSequence (wlen : Nat) (is : List Nat) : Prog isa :=
  is.foldr (fun i rest=>.seq (.block rounds)
    (.seq (.block ((if i<5 then squeeze i else []) ++ absorbCode wlen i)) rest)) (.block [])

private theorem sequence_ok {σ : State} {wlen : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work) (count start : Nat)
    {s : State} (h : CoreState σ wlen w1 work A B start s) :
    WP isa (coreSequence wlen (List.range' start count)) s
      (CoreState σ wlen w1 work A B (start+count)) := by
  induction count generalizing start s with
  | zero =>
    change WP isa (.block []) s (CoreState σ wlen w1 work A B start)
    exact WP.block_nil h
  | succ count ih =>
    simp only [List.range'_succ,coreSequence,List.foldr_cons]
    rw [WP.seq_iff]
    have hs := coreStep_ok hc h
    rw [WP.seq_iff] at hs
    refine WP.mono hs fun a ha=>?_
    rw [WP.seq_iff]
    refine WP.mono ha fun b hb=>?_
    have hh := ih (start+1) hb
    rw [show start+1+count=start+(count+1) by omega] at hh
    exact hh

/-- Exact selected unrolled schedule: seven permutations for ML-DSA-65,
nine for ML-DSA-87, with only five cached-mask squeeze blocks. -/
theorem core_ok {σ s : State} {wlen : Nat} {w1 work : Addr} {A B : Spec.Sha3.State}
    (hc : CoreConfig σ wlen w1 work) (h : CoreState σ wlen w1 work A B 0 s) :
    WP isa (coreFor wlen) s (CoreState σ wlen w1 work A B ((64+wlen)/136+1)) := by
  have he : coreFor wlen=coreSequence wlen (List.range ((64+wlen)/136+1)) := rfl
  rw [he,List.range_eq_range']
  simpa only [Nat.zero_add] using sequence_ok hc ((64+wlen)/136+1) 0 h

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
