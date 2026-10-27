module

public import VerifiedGarbage.Impl.Dsa.X86_64.ProbablePrime
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Offset

/-! # The probable-prime test keeps the callee-saved registers in its frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.X86_64.Spill VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.ProbablePrime

def spillSlots : List (Reg × Nat) :=
  [(.rbx, 0), (.rbp, 8), (.r12, 16), (.r13, 24), (.r14, 32), (.r15, 40)]

theorem spillSlots_fit : ∀ p ∈ spillSlots, p.2 + 8 ≤ 56 := by decide

theorem save_ok {s : State} (hw : (⟨s.gpr .rsp, 56⟩ : Region) ∈ s.wr) :
    WP isa (.block saveRegisters) s fun t =>
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Saved t.mem (s.gpr .rsp) s.gpr spillSlots ∧
      Frame [⟨s.gpr .rsp, 48⟩] s.mem t.mem := by
  change WP isa (.block (saveCode .rsp spillSlots)) s _
  apply WP.mono (VG.X86_64.Spill.save_ok .rsp spillSlots s (fun p hp =>
    ⟨_, hw, Offset.contains_base _ (spillSlots_fit p hp) (by have := spillSlots_fit p hp; omega)⟩))
  intro t ⟨hg, hr, hw, hm⟩
  refine ⟨hg, hr, hw, ?_, ?_⟩
  · rw [hm]; exact saveMem_saved _ _ _ _ (by decide)
  · rw [hm]; exact saveMem_frame_base _ _ _ _ (fun p hp => by revert p; decide) (by decide)

theorem restore_ok {s : State} (g : Reg → BitVec 64)
    (hw : (⟨s.gpr .rsp, 56⟩ : Region) ∈ s.wr)
    (hs : Saved s.mem (s.gpr .rsp) g spillSlots) :
    WP isa (.block restoreRegisters) s fun t =>
      (∀ r ∈ spillSlots.map Prod.fst, t.gpr r = g r) ∧
      (∀ r, r ∉ spillSlots.map Prod.fst → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  change WP isa (.block (restoreCode .rsp spillSlots)) s _
  exact VG.X86_64.Spill.restore_ok .rsp spillSlots g s (by decide) (fun p hp =>
    ⟨_, List.mem_append_right _ hw, Offset.contains_base _ (spillSlots_fit p hp)
      (by have := spillSlots_fit p hp; omega)⟩) hs

end VG.Proof.Dsa.X86_64.ProbablePrime
