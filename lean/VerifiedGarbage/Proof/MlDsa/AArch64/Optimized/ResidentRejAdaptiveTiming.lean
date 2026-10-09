import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPrefixTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTimingDone

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

abbrev Flagged (v blocks n : Nat) (σ s : State) :=
  Rows v blocks σ (fun k => prefixRow σ k n) s ∧
  Flags v (fun k => prefixRow σ k n) s

theorem flags_zero_eq {v n : Nat} {σ τ s t : State} (pub : Pub v σ τ)
    (hs : Flags v (fun k => prefixRow σ k n) s)
    (ht : Flags v (fun k => prefixRow τ k n) t) :
    (s.gpr .x27==0#64)=(t.gpr .x27==0#64) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,hs.zero,ht.zero]
  constructor
  · intro h k hk; rw [←pub.prefix hk n]; exact h k hk
  · intro h k hk; rw [pub.prefix hk n]; exact h k hk

theorem flagsFour_relCT {blocks n : Nat} {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (PrefixPair 4 blocks n σ τ) (.block Four.flags)
      (fun s t => Flagged 4 blocks n σ s ∧ Flagged 4 blocks n τ t) :=
  env_relCT pub (fun _ h => h.env) (fun _ h => h.env) flagsFour_ct
    (fun _ h => flagsSemantic_ok hp h) (fun _ h => flagsSemantic_ok hq h)

theorem adaptiveFour_relCT {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => Flagged 4 5 840 σ s ∧ Flagged 4 5 840 τ t)
      (.ite (.zero .x .x27) (.block [])
        (.seq (Four.squeezeN step 840 1)
          (.seq (Four.batch 0 840 56) (.block Four.flags))))
      (fun s t => TimingDone 4 σ s ∧ TimingDone 4 τ t) := by
  have ct : RelCT isa (fun s t => Flagged 4 5 840 σ s ∧ Flagged 4 5 840 τ t)
      (.ite (.zero .x .x27) (.block [])
        (.seq (Four.squeezeN step 840 1)
          (.seq (Four.batch 0 840 56) (.block Four.flags))))
      (fun _ _ => True) := by
    apply RelCT.ite
    · intro s t h
      rw [eval_zero,eval_zero]
      exact congrArg some (flags_zero_eq pub h.1.2 h.2.2)
    · exact RelCT.block_nil (fun _ _ _ => True.intro)
    · apply RelCT.seq (R := PrefixPair 4 6 840 σ τ)
      · exact (env_relCT pub (fun _ h => h.env) (fun _ h => h.env) sixthFour_ct
          (fun _ h => sixthFour_ok hp h) (fun _ h => sixthFour_ok hq h)).mono
          (fun _ _ h => ⟨h.1.1.1,h.1.2.1⟩) (fun _ _ h => h)
      · apply RelCT.seq (prefixFour_relCT hp hq pub (by decide : 840+3*56≤168*6)
          (by decide) (by decide) lastChecks)
        exact (flagsFour_relCT hp hq pub).mono (fun _ _ h => h) (fun _ _ _ => True.intro)
  exact (ct.wp (fun _ _ h => ⟨adaptiveFour_timingDone hp h.1.1 h.1.2,
    adaptiveFour_timingDone hq h.2.1 h.2.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem flagsTwo_relCT {blocks n : Nat} {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (PrefixPair 2 blocks n σ τ) (.block Two.flags)
      (fun s t => Flagged 2 blocks n σ s ∧ Flagged 2 blocks n τ t) :=
  env_relCT pub (fun _ h => h.env) (fun _ h => h.env) flagsTwo_ct
    (fun _ h => flagsSemantic_ok hp h) (fun _ h => flagsSemantic_ok hq h)

theorem adaptiveTwo_relCT {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => Flagged 2 5 840 σ s ∧ Flagged 2 5 840 τ t)
      (.ite (.zero .x .x27) (.block [])
        (.seq (Two.squeezeN Two.step 840 1)
          (.seq (Two.batch 0 840 56) (.block Two.flags))))
      (fun s t => TimingDone 2 σ s ∧ TimingDone 2 τ t) := by
  have ct : RelCT isa (fun s t => Flagged 2 5 840 σ s ∧ Flagged 2 5 840 τ t)
      (.ite (.zero .x .x27) (.block [])
        (.seq (Two.squeezeN Two.step 840 1)
          (.seq (Two.batch 0 840 56) (.block Two.flags))))
      (fun _ _ => True) := by
    apply RelCT.ite
    · intro s t h
      rw [eval_zero,eval_zero]
      exact congrArg some (flags_zero_eq pub h.1.2 h.2.2)
    · exact RelCT.block_nil (fun _ _ _ => True.intro)
    · apply RelCT.seq (R := PrefixPair 2 6 840 σ τ)
      · exact (env_relCT pub (fun _ h => h.env) (fun _ h => h.env) sixthTwo_ct
          (fun _ h => sixthTwo_ok hp h) (fun _ h => sixthTwo_ok hq h)).mono
          (fun _ _ h => ⟨h.1.1.1,h.1.2.1⟩) (fun _ _ h => h)
      · apply RelCT.seq (prefixTwo_relCT hp hq pub (by decide : 840+3*56≤168*6)
          (by decide) (by decide) (fun k hk => lastChecks k (by omega)))
        exact (flagsTwo_relCT hp hq pub).mono (fun _ _ h => h) (fun _ _ _ => True.intro)
  exact (ct.wp (fun _ _ h => ⟨adaptiveTwo_timingDone hp h.1.1 h.1.2,
    adaptiveTwo_timingDone hq h.2.1 h.2.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
