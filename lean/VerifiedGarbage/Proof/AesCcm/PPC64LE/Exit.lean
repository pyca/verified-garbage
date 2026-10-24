module

public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Entry

/-!
# AES-CCM on PPC64LE: the exit

Untrusted: everything here is checked by Lean. `restore` reloads the return
address and our caller's registers from the slots the entry filled at
`W + 128` (`exit_wp`), `r14`, the base, last.
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCcm.PPC64LE
open VG.PPC64LE.Spill (Saved restoreCode restore_wp)
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_ld wp_mtlr)

theorem saved_sub : ∀ p ∈ saved, p ∈ savedL := fun _ hp => List.mem_cons_of_mem _ hp

theorem other_of_preserved : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → r ∈ otherRegs := by decide

theorem saved_ne_r0 : ∀ p ∈ saved, p.1 ≠ .r0 := by decide

/-- `restore`: our caller's registers and return address back, for `s₀` the
state at the entry. -/
theorem exit_wp {c : Cx} {s₀ s : State} (E : Env c s) (sv : Saved c.W (saveG s₀) savedL s.mem)
    (hsp : s.sp = s₀.sp) (ho : ∀ r ∈ otherRegs, s.gpr r = s₀.gpr r) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .r3 = s.gpr .r3 := by
  unfold restore
  simp only [List.cons_append, List.nil_append]
  refine wp_ld (a := c.W + BitVec.ofNat 64 lrO) (by decide) (by decide) (by rw [E.r14])
    (E.perm.wR (by decide)) fun s₁ u₁ => wp_mtlr fun s₂ u₂ => ?_
  change WP isa (.block (restoreCode .r14 saved)) s₂ _
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have g₂ : ∀ r, r ≠ .r0 → s₂.gpr r = s.gpr r := fun r h => by rw [u₂.gpr, u₁.other _ h]
  have sv₂ : Saved c.W (saveG s₀) saved s₂.mem := by rw [m₂]; exact sv.sub saved_sub
  refine WP.mono (restore_wp (b := .r14) (B := c.W) (by decide) (by rw [g₂ _ (by decide), E.r14]) (by decide)
    (by decide) (fun p hp => by
      have := saved_bound p hp
      rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
      exact E.perm.wR (by omega)) sv₂) fun s' R => ?_
  have lr₂ : s₂.lr = s₀.lr := by
    rw [u₂.lr, u₁.gpr, sv (.r0, lrO) List.mem_cons_self]
    simp [saveG, State.write]
  refine ⟨⟨fun r hr => ?_, by rw [R.sp, u₂.sp, u₁.sp, hsp], by rw [R.lr, lr₂]⟩, by rw [R.mem, m₂],
    by rw [R.other _ (by decide), g₂ _ (by decide)]⟩
  by_cases hs : r ∈ saved.map Prod.fst
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
    rw [R.gpr p hp]
    simp [saveG, State.write, saved_ne_r0 p hp]
  · have hr0 : r ≠ .r0 := fun h => by subst h; exact absurd hr (by decide)
    rw [R.other r hs, g₂ r hr0, ho r (other_of_preserved r hr hs)]

end VG.Proof.AesCcm.PPC64LE
