module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Witness
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParentDifference
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SavedContext
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! Retained parent values needed by every RSA-compatible witness iteration. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

structure WitnessContext (base : Addr) (n candidate : Nat) (s : State) : Prop where
  parent : ParentContext base n candidate s
  ordinary : wordsVal s.mem base (slot n 3) n = 1
  square : wordsVal s.mem base (slot n 4) n = 2 ^ (64 * n) * 2 ^ (64 * n) % candidate
  ceiling : wordsVal s.mem base (slot n 1) n = candidate - 1

theorem WitnessContext.frame_keep {s t : State} {base : Addr} {n candidate : Nat}
    {rs : List Region} {regs : List Reg} (C : WitnessContext base n candidate s)
    (K : Keeps regs s t) (edi : .edi ∉ regs) (esp : .esp ∉ regs) (F : Frame rs s.mem t.mem)
    (apart : ∀ r ∈ rs, Region.Disjoint ⟨base, montgomeryBytes⟩ r) : WitnessContext base n candidate t :=
  ⟨C.parent.frame_keep K edi esp F apart,
    (C.parent.frame_slot F apart (show 3 < 9 by decide)).trans C.ordinary,
    (C.parent.frame_slot F apart (show 4 < 9 by decide)).trans C.square,
    (C.parent.frame_slot F apart (show 1 < 9 by decide)).trans C.ceiling⟩

theorem witness_init {s : State} {base : Addr} {bytes n candidate : Nat}
    (scr : Scr s base bytes) (capacity : montgomeryBytes ≤ bytes)
    (C : SavedContext base n candidate s) (positive : 0 < n) :
    WP isa (witnessInit n) s fun t =>
      WitnessContext base n candidate t ∧ Outside base (slot n 1) (8 * n) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have ordinary : val32 s.mem base (slot n 3) (2 * n) = 1 := by
    rw [← wordsVal_eq_val32]; exact C.ordinary
  refine WP.mono (parent_difference_at scr capacity C.parent positive (show 1 < 9 by decide)
    (show 3 < 9 by decide) (by decide) (by decide) ordinary C.parent.gt_one)
    fun t ⟨P, value, F, K⟩ => ?_
  have same : ∀ j, j = 3 ∨ j = 4 → wordsVal t.mem base (slot n j) n = wordsVal s.mem base (slot n j) n := by
    intro j hj
    have apart := slot_le (n := n) (i := 1) (j := j) (by omega)
    have bound := slot_bound (n := n) (i := j) (by omega)
    have size := C.parent.size_le
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact F.val32 (.inr (by unfold stride at apart; omega)) (by
      unfold stride at bound; unfold montgomeryBytes at size; omega)
  refine ⟨⟨P, (same 3 (.inl rfl)).trans C.ordinary, (same 4 (.inr rfl)).trans C.square, ?_⟩, F, K⟩
  rw [wordsVal_eq_val32]; exact value

end VG.Proof.Dsa.X86.Generation
