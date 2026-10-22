module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialPairStep

/-! Stop a public candidate's trial filter at the first dividing prime pair. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen

theorem trial_until_step {P : TrialPlan} {initial s : State} {sp : BitVec 32} {k : Nat}
    (I : TrialLoopInv P initial sp k s) (hk : k < P.count)
    (table : ∀ i < P.count, initial.mem.readW (off P.base (P.table + 4 * i)) 32 = BitVec.ofNat 32 (tabWord32 i)) :
    WP isa trialPairUntil s fun t => TrialLoopInv P initial sp (k + 1) t ∧
      t.zf = some (decide (k + 1 = P.count ∨ tr (2 * (k + 1)) (P.number initial) = true)) := by
  unfold trialPairUntil
  refine WP.seq (WP.mono (trial_pair_step I hk table) fun a ⟨Ia, zf⟩ => ?_)
  refine WP.ite (decide (k + 1 = P.count)) zf ?_ ?_
  · intro h
    have done := of_decide_eq_true h
    exact WP.block_nil ⟨Ia, by simpa only [done, true_or, decide_true] using zf⟩
  · intro h
    have more := of_decide_eq_false h
    obtain ⟨values, A⟩ := Ia
    refine wp_movS (A.machine.read (i := 5) (by decide)) fun b B _ =>
      wp_cmpS rfl fun t T last => WP.block_nil ?_
    have K : Keeps [.eax] a t := B.keeps.trans (T.keeps _)
    have mem : t.mem = a.mem := T.mem.trans B.mem
    refine ⟨⟨values, A.machine.of_keeps K (by decide) mem, A.start, A.last, A.table, A.count, A.flag⟩, ?_⟩
    rw [last, B.gpr, A.flag]
    cases flag : tr (2 * (k + 1)) (P.number initial) <;>
      simp only [more, false_or, Bool.false_eq_true, decide_false, decide_true] <;> rfl

end VG.Proof.Dsa.X86.Generation
