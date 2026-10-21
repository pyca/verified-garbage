module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBody
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment

/-! # Candidate workspace writes and nested frames retain the saved cdecl registers -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem saved_stack_far {E : Environment} (v : E.Valid) :
    (⟨E.p.setWidth 64, 16⟩ : Region).Disjoint (below E.p 96) := by
  unfold below
  rw [Taint.sub_setWidth v.low]
  exact Offset.base_disjoint_below _ (by decide)

theorem saved_read {E : Environment} (v : E.Valid) {s t : State}
    (fit : 16 ≤ (s.gpr .esp).toNat) (sp : (Compact.entered s).gpr .esp = E.p)
    (F : MutableFrame E (Compact.entered s).mem t.mem) {i : Nat} (index : i < 4) :
    t.mem.readW (addr E.p (4 * i)) 32 = s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega)) := by
  have pFit : E.p.toNat + 16 ≤ 2 ^ 32 := by
    rw [← sp, Compact.entered, pushed_esp]
    change (s.gpr .esp - 16#32).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat fit]
    have := (s.gpr .esp).isLt
    omega
  have same := F.readW (r := (⟨E.p.setWidth 64, 16⟩ : Region)) (a := addr E.p (4 * i)) (w := 32)
    (by rw [addr_eq (by omega)]; exact Offset.contains_base _ (by omega) (by omega)) (by
      intro r mem
      rcases List.mem_append.mp mem with mem | mem
      · exact (v.savedFar r (List.mem_append_left _ mem)).symm
      · obtain rfl := List.mem_singleton.mp mem
        exact saved_stack_far v) (by decide)
  have word := pushed_word (rs := Compact.savedRegisters) (by decide) fit index
  change (Compact.entered s).mem.readW (addr ((Compact.entered s).gpr .esp) (4 * i)) 32 = _ at word
  rw [sp] at word
  exact same.trans word

theorem return_read {E : Environment} (_v : E.Valid) {s t : State}
    (fit : 112 ≤ (s.gpr .esp).toNat) (sp : (Compact.entered s).gpr .esp = E.p)
    (returnFar : ∀ r ∈ E.writeRegions, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r)
    (F : MutableFrame E (Compact.entered s).mem t.mem) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  have outside : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (s.gpr .esp) 112) := by
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.base_disjoint_below _ (by decide)
  have inner : (below E.p 96).Sub (below (s.gpr .esp) 112) := by
    rw [← sp, Compact.entered, pushed_esp]
    exact below_inner (by decide) fit
  have same := F.readW (w := 32) (Region.contains_self ((s.gpr .esp).setWidth 64) 4) (by
    intro r mem
    rcases List.mem_append.mp mem with mem | mem
    · exact returnFar r mem
    · obtain rfl := List.mem_singleton.mp mem
      exact outside.sub_right inner) (by decide)
  have pushed := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) (by change 16 ≤ _; omega)
  exact same.trans (pushed.readW (Region.contains_self _ _) (by
    intro r mem; obtain rfl := List.mem_singleton.mp mem
    exact outside.sub_right (below_sub (by decide) fit)) (by decide))

end VG.Proof.RsaKeyGen.X86.Candidate
