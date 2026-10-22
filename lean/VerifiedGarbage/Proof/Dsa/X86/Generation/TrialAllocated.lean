module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialArguments
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! Save EDI separately from the existing 36-byte trial frame. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.MillerRabin.X86 VG.Proof.Mont.X86

abbrev trialAllocated (s : State) : State := allocFrame 36 (pushed [.edi] s)

structure TrialSetup (s : State) (n : Nat) (t : State) : Prop where
  args : ArgumentState (trialAllocated s) (trialArgument ((trialAllocated s).gpr .edi) n) 4 t

theorem trial_sequence_noSp {n : Nat} {body : Prog isa} (noSp : NoSp body) :
    NoSp (.seq (.block (trialArguments n)) body : Prog isa) := by
  have arguments : NoSp (.block (trialArguments n) : Prog isa) := NoSp.of_all (by rfl)
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact arguments i hi
  · exact noSp i hi

theorem trial_alloc_noSp {n : Nat} {body : Prog isa} (noSp : NoSp body) :
    NoSp (.frame (.alloc 36) (.seq (.block (trialArguments n)) body) (.free 36) : Prog isa) := by
  intro i hi
  simp only [instrs, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | hi | rfl
  · rfl
  · exact trial_sequence_noSp (n := n) noSp i (List.mem_append.mpr hi)
  · rfl

theorem with_trial {s : State} {n : Nat} {body : Prog isa} {Q : State → Prop}
    (low : 40 ≤ (s.gpr .esp).toNat) (noSp : NoSp body)
    (run : ∀ t, TrialSetup s n t → WP isa body t fun u => Q (popped .edi 1 (freed 36 u))) :
    WP isa (withTrial n body) s Q := by
  unfold withTrial
  refine WP.frame (by decide) (by decide) (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
    (trial_alloc_noSp noSp) ?_
  have pushedLow : 36 ≤ ((pushed [.edi] s).gpr .esp).toNat := by
    rw [pushed_esp, VG.X86.sub_toNat (by simpa using (show 4 ≤ (s.gpr .esp).toNat by omega))]
    simp only [List.length_cons, List.length_nil]
    omega
  refine WP.frameAlloc (by decide) (by decide) (by decide) pushedLow (trial_sequence_noSp noSp) ?_
  have fit : ((trialAllocated s).gpr .esp).toNat + 36 ≤ 2 ^ 32 := by
    rw [allocFrame_esp, VG.X86.sub_toNat pushedLow]
    have := ((pushed [.edi] s).gpr .esp).isLt
    omega
  refine WP.seq (WP.mono (trial_arguments (n := n) fit
    (by rw [allocFrame_wr]; exact List.mem_cons_self ..)) fun t args => ?_)
  exact run t ⟨args⟩

end VG.Proof.Dsa.X86.Generation
