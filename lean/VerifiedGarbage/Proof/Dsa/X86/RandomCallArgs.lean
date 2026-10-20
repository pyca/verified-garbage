module
public import VerifiedGarbage.Impl.Dsa.X86.RandomSign
public import VerifiedGarbage.Proof.Dsa.X86.RandomCallPre
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Mont.X86.Instr

/-!
# The signer's arguments (x86)

`callArgs` copies the caller's arguments the signer takes, and the nonce's
address, to the frame's first eleven words (`CallSlots`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random VG.Impl.Dsa.X86.RandomSign

/-- One argument's copy. -/
theorem copyArg_ok {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) {j i : Nat} (hj : j < 13)
    (hi : 4 * i + 4 ≤ 44) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Ready s₀ u → u.mem = t.mem.writeW (off (rBase s₀) (4 * i)) (X86.arg s₀ j) →
      Keeps [.eax] t u → WP isa (.block is) u Q) :
    WP isa (.block (copyArg j i ++ is)) t Q := by
  unfold copyArg
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (h.argSrc A hj) fun u₁ v₁ _ => ?_
  have h₁ := h.upd v₁ (by decide)
  refine wp_slot h₁.rf (by unfold Random.frameBytes; omega) v₁.gpr fun u₂ f₂ m₂ g₂ r₂ w₂ _ _ => ?_
  refine k u₂ (h₁.congr (rs := []) ⟨fun r _ => by rw [g₂], r₂, w₂⟩
    (by rw [m₂]; exact frame_store s₀ _ (by unfold Random.frameBytes; omega) _)) (by rw [m₂, v₁.mem])
    (v₁.keeps.trans ⟨fun r _ => by rw [g₂], r₂, w₂⟩)

/-- The memory after `callArgs`, from `m`, with the stack pointer `sp`. -/
def argsMem (s₀ : State) (m : Mem) (sp : BitVec 32) : Mem :=
  (((((((((((m.writeW (off (rBase s₀) (4 * 0)) (X86.arg s₀ 0)).writeW (off (rBase s₀) (4 * 1)) (X86.arg s₀ 1)).writeW
    (off (rBase s₀) (4 * 2)) (X86.arg s₀ 3)).writeW (off (rBase s₀) (4 * 3)) (X86.arg s₀ 4)).writeW
    (off (rBase s₀) (4 * 4)) (X86.arg s₀ 5)).writeW (off (rBase s₀) 20) (sp + BitVec.ofNat 32 oNonce)).writeW
    (off (rBase s₀) (4 * 6)) (X86.arg s₀ 6)).writeW (off (rBase s₀) (4 * 7)) (X86.arg s₀ 7)).writeW
    (off (rBase s₀) (4 * 8)) (X86.arg s₀ 8)).writeW (off (rBase s₀) (4 * 9)) (X86.arg s₀ 11)).writeW
    (off (rBase s₀) (4 * 10)) (X86.arg s₀ 12))

theorem argsMem_slots (s₀ : State) (m : Mem) (sp : BitVec 32) :
    ∀ i < 11, slot (argsMem s₀ m sp) (rBase s₀) (4 * i) = callVal s₀ sp i := by
  intro i hi
  unfold argsMem
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ =>
    simp (disch := decide) only [slot_write_self, slot_write_ne, Nat.reduceMul, callVal]

/-- A store within the range `(o, n)`. -/
theorem store_in (B : Addr) (m : Mem) {d o n : Nat} (v : BitVec 32) {rs : List (Nat × Nat)}
    (hm : (o, n) ∈ rs) (h₁ : o ≤ d) (h₂ : d + 4 ≤ o + n) (hb : d + 4 ≤ 2 ^ 64) :
    Outs B rs m (m.writeW (off B d) v) :=
  Outs.of_outside ((writeW32_outside m B v hb).mono h₁ h₂) hm

theorem argsMem_outs (s₀ : State) (m : Mem) (sp : BitVec 32) : Outs (rBase s₀) [(0, 44)] m (argsMem s₀ m sp) := by
  unfold argsMem
  have e := fun {m : Mem} {d : Nat} (v : BitVec 32) (h : d + 4 ≤ 44) =>
    store_in (rBase s₀) m (rs := [(0, 44)]) (o := 0) (n := 44) (d := d) v (List.mem_singleton_self _)
      (Nat.zero_le _) h (by omega)
  exact ((((((((((e _ (by decide)).trans (e _ (by decide))).trans (e _ (by decide))).trans
    (e _ (by decide))).trans (e _ (by decide))).trans (e _ (by decide))).trans
    (e _ (by decide))).trans (e _ (by decide))).trans (e _ (by decide))).trans
    (e _ (by decide))).trans (e _ (by decide))

theorem callArgs_ok {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ u, Ready s₀ u → u.mem = argsMem s₀ t.mem (t.gpr .esp) → Keeps [.eax] t u → WP isa (.block is) u Q) :
    WP isa (.block (callArgs ++ is)) t Q := by
  unfold callArgs
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine copyArg_ok A h (by decide) (by decide) fun u₁ h₁ m₁ k₁ => ?_
  refine copyArg_ok A h₁ (by decide) (by decide) fun u₂ h₂ m₂ k₂ => ?_
  refine copyArg_ok A h₂ (by decide) (by decide) fun u₃ h₃ m₃ k₃ => ?_
  refine copyArg_ok A h₃ (by decide) (by decide) fun u₄ h₄ m₄ k₄ => ?_
  refine copyArg_ok A h₄ (by decide) (by decide) fun u₅ h₅ m₅ k₅ => ?_
  refine wp_movS rfl fun u₆ v₆ _ => wp_addi fun u₇ v₇ => ?_
  have h₇ := (h₅.upd v₆ (by decide)).upd v₇ (by decide)
  refine wp_slot h₇.rf (by decide) v₇.gpr fun u₈ f₈ m₈ g₈ r₈ w₈ _ _ => ?_
  have k₈ : Keeps [.eax] u₅ u₈ := ((v₆.keeps).trans v₇.keeps).trans ⟨fun r _ => by rw [g₈], r₈, w₈⟩
  have h₈ : Ready s₀ u₈ := h₅.congr k₈ (by
    rw [m₈, v₇.mem, v₆.mem]; exact frame_store s₀ _ (by decide) _)
  refine copyArg_ok A h₈ (by decide) (by decide) fun u₉ h₉ m₉ k₉ => ?_
  refine copyArg_ok A h₉ (by decide) (by decide) fun u₁₀ h₁₀ m₁₀ k₁₀ => ?_
  refine copyArg_ok A h₁₀ (by decide) (by decide) fun u₁₁ h₁₁ m₁₁ k₁₁ => ?_
  refine copyArg_ok A h₁₁ (by decide) (by decide) fun u₁₂ h₁₂ m₁₂ k₁₂ => ?_
  refine copyArg_ok A h₁₂ (by decide) (by decide) fun u₁₃ h₁₃ m₁₃ k₁₃ => ?_
  have kk : Keeps [.eax] t u₁₃ := (((((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₈).trans k₉).trans
    k₁₀).trans k₁₁).trans k₁₂).trans k₁₃
  refine k u₁₃ h₁₃ ?_ kk
  have esp : u₅.gpr .esp = t.gpr .esp := ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).1 _ (by decide)
  rw [m₁₃, m₁₂, m₁₁, m₁₀, m₉, m₈, v₇.mem, v₆.mem, m₅, m₄, m₃, m₂, m₁, v₆.gpr, esp]
  rfl

end VG.Proof.Dsa.X86
