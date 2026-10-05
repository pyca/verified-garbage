import VerifiedGarbage.Proof.AesSiv.X86.Callee
import VerifiedGarbage.Proof.AesGcm.X86.Top

/-!
# AES-SIV on x86: the entry of `encrypt` and `decrypt`

Untrusted: everything here is checked by Lean. The entry (`entry_ok`) saves
our caller's registers in `W` (AES-GCM's `save_ok`), copies the stack
arguments into their slots (`keeps_ok`): the slots (`Slots`) hold the
arguments. The exit is AES-GCM's (`exit_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt)
open VG.Proof.AesGcm.X86 (w64 slotv argA argsR argA_contains argA_sub SavedAt save_ok KeepEnv keeps_ok keepR
  runBlock_app_of in_off)

/-- The arguments the entry copies, and where. -/
abbrev entryPs : List (Nat × Nat) :=
  [(0, ctxO), (1, roundsO), (2, adsO), (3, leftO), (4, dataO), (5, lenO)]

theorem sivEntry_eq : sivEntry = entry 7 (entryPs.flatMap (fun p => keep p.1 p.2)) := rfl

/-- What the entry leaves. -/
structure Entered (s : State) (W : BitVec 32) (s' : State) : Prop where
  ebp : s'.gpr .ebp = W
  esp : s'.gpr .esp = s.gpr .esp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : SavedAt s'.mem W s
  slots : ∀ p ∈ entryPs, slotv s'.mem W p.2 = arg s p.1
  frame : Frame [⟨w64 W + BitVec.ofNat 64 128, 2432⟩] s.mem s'.mem

/-- The entry, from `W` (the stack argument 7). -/
theorem entry_ok {s : State} {W : BitVec 32} (hW : arg s 7 = W) (wW : Covers [⟨w64 W, 2560⟩] s.wr)
    (rA : Covers [argsR (s.gpr .esp) 8] (s.rd ++ s.wr)) (aw : (argsR (s.gpr .esp) 8).Disjoint ⟨w64 W, 2560⟩)
    (fa : (s.gpr .esp).toNat + 4 + 4 * 8 ≤ 2 ^ 32) (fw : W.toNat + 2560 ≤ 2 ^ 32) :
    WP isa sivEntry s (Entered s W) := by
  rw [sivEntry_eq]
  generalize hSP : s.gpr .esp = SP at rA aw fa
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 7) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.seq (WP.of_runBlock ⟨_, by crun [hSP, i₀], ?_⟩)
  have hax : (s.setReg .eax (s.mem.readW (argA SP 7) 32)).gpr .eax = W := by
    rw [gpr_setReg_self, ← hSP]; exact hW
  set s₀ := s.setReg .eax (s.mem.readW (argA SP 7) 32) with hs₀
  obtain ⟨s₁, run₁, bp₁, g₁, rd₁, wr₁, sv₁, f₁⟩ := save_ok s₀ hax (by rw [hs₀]; exact wW) fw
  have sp₁ : s₁.gpr .esp = SP := by rw [g₁ _ (by decide), hs₀, gpr_setReg_of_ne _ _ (by decide), hSP]
  have f₁' : Frame [⟨w64 W + BitVec.ofNat 64 128, 16⟩] s.mem s₁.mem := f₁
  have argW : ∀ {i}, i < 8 → ∀ {d k : Nat}, d + k ≤ 2560 → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region)],
      (⟨argA SP i, 4⟩ : Region).Disjoint r := fun hi _ _ hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (aw.sub_left (argA_sub hi fa)).sub_right (Offset.sub_base _ hk)
  have hA₁ : ∀ i < 8, s₁.mem.readW (argA SP i) 32 = arg s i := fun i hi => by
    rw [f₁'.readW (r := ⟨argA SP i, 4⟩) (Region.contains_self _ _) (argW hi (by decide)) (by decide)]
    rw [arg, argAddr, hSP]
  have ke : KeepEnv W SP 8 s₁ := ⟨bp₁, sp₁, by rw [wr₁]; exact wW, by rw [rd₁, wr₁]; exact rA, aw, fa, fw⟩
  obtain ⟨s₃, run₃, sl₃, f₃, g₃, rd₃, wr₃⟩ := keeps_ok entryPs (fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by decide) ke
  have bp₃ : s₃.gpr .ebp = W := by rw [g₃ _ (by decide), bp₁]
  have sp₃ : s₃.gpr .esp = SP := by rw [g₃ _ (by decide), sp₁]
  refine WP.of_runBlock ⟨_, runBlock_app_of run₁ run₃, ?_⟩
  -- What the entry wrote.
  have f₃' : Frame [⟨w64 W + BitVec.ofNat 64 128, 2432⟩] s.mem s₃.mem := by
    refine (f₁'.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hsv : SavedAt s₃.mem W s := by
    have := sv₁.frame f₃ fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    obtain ⟨a, b, c, d⟩ := this
    refine ⟨a.trans ?_, b.trans ?_, c.trans ?_, d.trans ?_⟩ <;>
      simp only [hs₀, gpr_setReg_of_ne _ _ (by decide : Reg.ebx ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.esi ≠ .eax),
        gpr_setReg_of_ne _ _ (by decide : Reg.edi ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.ebp ≠ .eax)]
  refine ⟨bp₃, by rw [sp₃, hSP], by rw [rd₃, rd₁]; rfl, by rw [wr₃, wr₁]; rfl, hsv, ?_, f₃'⟩
  intro p hp
  have e := sl₃ p hp
  have hp1 : p.1 < 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [hA₁ p.1 hp1] at e
  exact e

end VG.Proof.AesSiv.X86
