module

import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallArgs
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Dsa.X86.GenerateKey
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.State

/-! # Save registers and initialize key-generation consumption and status -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.GenerateKey

/-- Save the callee-saved registers, and start the counts. -/
theorem entry_ok {s₀ t : State} (h : Ready s₀ t) (hb : t.gpr .ebx = s₀.gpr .ebx) (hs : t.gpr .esi = s₀.gpr .esi)
    (hd : t.gpr .edi = s₀.gpr .edi) (hp : t.gpr .ebp = s₀.gpr .ebp) :
    WP isa (.block entry) t fun u => Ready s₀ u ∧ Saved s₀ u.mem ∧
      slot u.mem (rBase s₀) oUsed = 0 ∧ slot u.mem (rBase s₀) oStatus = 0 ∧
      Outs (rBase s₀) [(oSaveEbx, 44)] t.mem u.mem := by
  unfold entry
  refine wp_slot h.rf (by decide) hb fun t₁ f₁ m₁ g₁ r₁ w₁ _ _ => ?_
  refine wp_slot f₁ (by decide) (v := s₀.gpr .esi) (by rw [g₁]; exact hs) fun t₂ f₂ m₂ g₂ r₂ w₂ _ _ => ?_
  refine wp_slot f₂ (by decide) (v := s₀.gpr .edi) (by rw [g₂, g₁]; exact hd) fun t₃ f₃ m₃ g₃ r₃ w₃ _ _ => ?_
  refine wp_slot f₃ (by decide) (v := s₀.gpr .ebp) (by rw [g₃, g₂, g₁]; exact hp) fun t₄ f₄ m₄ g₄ r₄ w₄ _ _ => ?_
  refine wp_movS rfl fun t₅ u₅ _ => wp_slot (f₄.of_keeps u₅.keeps) (by decide) u₅.gpr
    fun t₆ f₆ m₆ g₆ r₆ w₆ _ _ => wp_slot f₆ (by decide) (v := (0 : BitVec 32)) (by rw [g₆]; exact u₅.gpr)
    fun t₈ f₈ m₈ g₈ r₈ w₈ _ _ => WP.block_nil ?_
  have hm : t₈.mem = (((((((t.mem.writeW (off (rBase s₀) oSaveEbx) (s₀.gpr .ebx)).writeW
      (off (rBase s₀) oSaveEsi) (s₀.gpr .esi)).writeW (off (rBase s₀) oSaveEdi) (s₀.gpr .edi)).writeW
      (off (rBase s₀) oSaveEbp) (s₀.gpr .ebp)).writeW (off (rBase s₀) oUsed) (0 : BitVec 32)).writeW
      (off (rBase s₀) oStatus) (0 : BitVec 32))) := by
    rw [m₈, m₆, u₅.mem, m₄, m₃, m₂, m₁]
  have kk : Keeps [.eax] t t₈ :=
    (((((Keeps.trans (⟨fun r _ => by rw [g₁], r₁, w₁⟩ : Keeps [.eax] t t₁) ⟨fun r _ => by rw [g₂], r₂, w₂⟩).trans
      ⟨fun r _ => by rw [g₃], r₃, w₃⟩).trans ⟨fun r _ => by rw [g₄], r₄, w₄⟩).trans u₅.keeps).trans
      ⟨fun r _ => by rw [g₆], r₆, w₆⟩).trans ⟨fun r _ => by rw [g₈], r₈, w₈⟩
  have e := fun {m : Mem} {d : Nat} (v : BitVec 32) (h₁ : oSaveEbx ≤ d) (h₂ : d + 4 ≤ oSaveEbx + 44) =>
    store_in (rBase s₀) m (rs := [(oSaveEbx, 44)]) v (List.mem_singleton_self _) h₁ h₂ (by unfold oSaveEbx at h₂; omega)
  refine ⟨h.congr kk (by
      rw [hm]
      exact (((((frame_store s₀ _ (by decide) _).trans (frame_store s₀ _ (by decide) _)).trans
        (frame_store s₀ _ (by decide) _)).trans (frame_store s₀ _ (by decide) _)).trans
        (frame_store s₀ _ (by decide) _)).trans (frame_store s₀ _ (by decide) _)),
    ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals first
    | (rw [hm]; simp (disch := decide) only [slot_write_self, slot_write_ne]; done)
    | (rw [hm]; exact (((((e _ (by decide) (by decide)).trans (e _ (by decide) (by decide))).trans
        (e _ (by decide) (by decide))).trans (e _ (by decide) (by decide))).trans
        (e _ (by decide) (by decide))).trans (e _ (by decide) (by decide)))

end VG.Proof.Dsa.X86.KeyRandom
