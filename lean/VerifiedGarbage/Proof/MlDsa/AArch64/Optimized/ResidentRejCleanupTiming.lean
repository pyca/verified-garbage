import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailReadyTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptiveTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFinish

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem failure_ready {v : Nat} {σ τ s t : State} (pub : Pub v σ τ)
    (hs : TimingDone v σ s) (ht : TimingDone v τ t)
    (hz : s.gpr .x27≠0#64) : TailReady v σ s ∧ TailReady v τ t := by
  have hn : t.gpr .x27≠0#64 := by
    intro he
    apply hz
    apply hs.done.flags.zero.mpr
    intro k hk
    rw [pub.prefix hk 1008]
    exact ht.done.flags.zero.mp he k hk
  exact ⟨⟨hs.done,hs.bytes hz⟩,⟨ht.done,ht.bytes hn⟩⟩

private theorem finish_ct : PointerCT [.x19]
    (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
      Impl.MlDsa.AArch64.Sample.Rej4.epi)) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem cleanupFour_relCT {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => TimingDone 4 σ s ∧ TimingDone 4 τ t) Four.tailZeros
      (fun s t => Done 4 σ s ∧ Done 4 τ t) := by
  unfold Four.tailZeros
  apply RelCT.ite
  · intro s t h
    rw [eval_zero,eval_zero]
    exact congrArg some (flags_zero_eq pub h.1.done.flags h.2.done.flags)
  · exact RelCT.block_nil (fun _ _ h => ⟨h.1.1.done,h.1.2.done⟩)
  · refine (tailRows_relCT hp hq pub (List.range 4) (by
      simpa only [List.mem_range] using fun k hk => hk)).mono ?_ (fun _ _ h => ⟨h.1.1,h.2.1⟩)
    intro s t h
    apply failure_ready pub h.1.1 h.1.2
    intro hz
    have he := h.2
    rw [eval_zero,hz] at he
    simp at he

theorem cleanupFinishFour_relCT {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => TimingDone 4 σ s ∧ TimingDone 4 τ t)
      (.seq Four.tailZeros
        (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
          Impl.MlDsa.AArch64.Sample.Rej4.epi))) (fun _ _ => True) := by
  apply RelCT.seq (cleanupFour_relCT hp hq pub)
  exact (env_relCT pub (fun _ h => h.env) (fun _ h => h.env) finish_ct
    (fun _ h => finish_ok hp h) (fun _ h => finish_ok hq h)).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)

theorem cleanupTwo_relCT {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => TimingDone 2 σ s ∧ TimingDone 2 τ t) Two.tailZeros
      (fun s t => Done 2 σ s ∧ Done 2 τ t) := by
  unfold Two.tailZeros
  apply RelCT.ite
  · intro s t h
    rw [eval_zero,eval_zero]
    exact congrArg some (flags_zero_eq pub h.1.done.flags h.2.done.flags)
  · exact RelCT.block_nil (fun _ _ h => ⟨h.1.1.done,h.1.2.done⟩)
  · refine (tailRows_relCT hp hq pub (List.range 2) (by
      simpa only [List.mem_range] using fun k hk => hk)).mono ?_ (fun _ _ h => ⟨h.1.1,h.2.1⟩)
    intro s t h
    apply failure_ready pub h.1.1 h.1.2
    intro hz
    have he := h.2
    rw [eval_zero,hz] at he
    simp at he

theorem cleanupFinishTwo_relCT {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => TimingDone 2 σ s ∧ TimingDone 2 τ t)
      (.seq Two.tailZeros
        (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
          Impl.MlDsa.AArch64.Sample.Rej4.epi))) (fun _ _ => True) := by
  apply RelCT.seq (cleanupTwo_relCT hp hq pub)
  exact (env_relCT pub (fun _ h => h.env) (fun _ h => h.env) finish_ct
    (fun _ h => finish_ok hp h) (fun _ h => finish_ok hq h)).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
