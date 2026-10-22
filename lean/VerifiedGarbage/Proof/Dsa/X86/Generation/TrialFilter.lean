module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialReturn
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! Invoke the public early-exit filter on the parent candidate using the shared prime table. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen

theorem trial_filter {s : State} {base : Addr} {bytes n candidate bits : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : CallRoom (s.gpr .esp) base bytes)
    (positive : 0 < n) (upper : n ≤ 48)
    (modulus : wordsVal s.mem base (slot n 0) n = candidate) (large : 8161 < candidate)
    (policy : 1024 < bits ↔ 16 < n)
    (table : ∀ i < trialWordCount n, s.mem.readW (off base (trialTableOffset + 4 * i)) 32 = BitVec.ofNat 32 (tabWord32 i)) :
    WP isa (trialFilter n) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite bits candidate).toNat ∧
      Frame [below (s.gpr .esp) 40] s.mem t.mem ∧ Keeps trialCallerClob s t := by
  let P := trialPlan base bytes n capacity positive upper
  have value : P.number (trialAllocated s) = candidate := by
    change val32 (trialAllocated s).mem base (slot n 0) (2 * n) = _
    rw [trial_allocated_val32 scr room (by have := P.candidateFits; change slot n 0 + 8 * n ≤ bytes at this; omega),
      ← wordsVal_eq_val32]
    exact modulus
  have tableAllocated : ∀ i < P.count, (trialAllocated s).mem.readW (off P.base (P.table + 4 * i)) 32 =
      BitVec.ofNat 32 (tabWord32 i) := by
    intro i hi
    change i < trialWordCount n at hi
    change (trialAllocated s).mem.readW (off base (trialTableOffset + 4 * i)) 32 = _
    rw [trial_allocated_word scr room (by have := P.tableFits; change trialTableOffset + 4 * trialWordCount n ≤ bytes at this; omega)]
    exact table i hi
  unfold trialFilter
  refine with_trial room.low (NoSp.of_all (by decide : trialLoopEarly.allInstrs (fun i => !Taint.clobbers i .esp) = true))
    fun g H => ?_
  obtain ⟨start, last, ptr, count⟩ := H.argument_values scr
  refine WP.mono (trial_loop_early_dsa (P := P) (H.machine scr room) start last ptr count tableAllocated rfl
    (by rw [value]; exact large) policy) fun u ⟨⟨k, _, _, I⟩, result⟩ => ?_
  obtain ⟨K, F, eax⟩ := trial_return room.low I.machine.memory I.machine.keeps
  rw [value] at result
  exact ⟨eax.trans result, F, K⟩

end VG.Proof.Dsa.X86.Generation
