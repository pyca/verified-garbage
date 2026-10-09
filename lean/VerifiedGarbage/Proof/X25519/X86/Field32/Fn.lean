import VerifiedGarbage.Proof.X25519.X86.Field32.Chain
import VerifiedGarbage.TCB.X86.Target

/-!
# `vg_gf25519_r32_pow250` on x86 (32-bit): what it computes

From its entry (`Entry`: the working space `ws` at `x`, its argument on the
stack), `entry` saves `ebx`, `esi`, `edi` and `ebp` at `SAVE`, points `edi`
at the working space and copies `a` to `AC` (`entry_ok`); the chain leaves
`a^(2^250 - 1)` in `E1` and `a^11` in `E0` (`chain_spec`); `exit` restores
the registers (`exit_ok`). `pow250Fn_ok`: the function keeps the
callee-saved registers, changes memory only in bytes 512 to 1023, and
leaves the two powers at bytes 544 and 512.
-/

namespace VG.Proof.X25519.X86.Field32

open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86 VG.Spec.X25519
open VG.Proof.X25519 (pw)

/-- The function's entry: the working space `ws = x` (its argument), writable
for 4096 bytes and within the 32-bit address space, and the argument
readable. -/
structure Entry (s : State) (x : BitVec 32) : Prop where
  ws : arg s 0 = x
  fit : x.toNat + 4096 ≤ 2 ^ 32
  wr : scR 4096 x ∈ s.wr
  read : InRegions (s.rd ++ s.wr) (argAddr s 0) 4

/-- The registers saved at `SAVE`. -/
structure Saved (x : BitVec 32) (g : Reg → BitVec 32) (m : Mem) : Prop where
  ebx : wd m x SAVE = g .ebx
  esi : wd m x (SAVE + 4) = g .esi
  edi : wd m x (SAVE + 8) = g .edi
  ebp : wd m x (SAVE + 12) = g .ebp

theorem below_AC : Below AC := by decide
theorem below_aAt : Below Spec.X25519.Field32.aAt := by decide

theorem save_ok {s : State} {x : BitVec 32} (h : Entry s x) :
    WP isa (.block [.mov .eax (.mem (at_ .esp 4)), .store (at_ .eax SAVE) .ebx,
      .store (at_ .eax (SAVE + 4)) .esi, .store (at_ .eax (SAVE + 8)) .edi,
      .store (at_ .eax (SAVE + 12)) .ebp, .mov .edi (.reg .eax)]) s fun t =>
      Ctx 4096 x t ∧ t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [sub x SAVE 16] s.mem t.mem ∧ Saved x s.gpr t.mem := by
  have hfit := h.fit
  refine Wp.wp_ldm (b := .esp) (o := 4 + 4 * 0) rfl h.read fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = x := by rw [u₁.gpr]; exact h.ws
  refine Wp.wp_stm e₁ ⟨_, by rw [u₁.wr]; exact h.wr, scR_contains hfit (by decide) (by decide)⟩ fun s₂ u₂ => ?_
  refine Wp.wp_stm (by rw [u₂.gpr]; exact e₁)
    ⟨_, by rw [u₂.wr, u₁.wr]; exact h.wr, scR_contains hfit (by decide) (by decide)⟩ fun s₃ u₃ => ?_
  refine Wp.wp_stm (by rw [u₃.gpr, u₂.gpr]; exact e₁)
    ⟨_, by rw [u₃.wr, u₂.wr, u₁.wr]; exact h.wr, scR_contains hfit (by decide) (by decide)⟩ fun s₄ u₄ => ?_
  refine Wp.wp_stm (by rw [u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁)
    ⟨_, by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact h.wr, scR_contains hfit (by decide) (by decide)⟩
    fun s₅ u₅ => ?_
  refine Wp.wp_mov fun s₆ u₆ => WP.block_nil ?_
  have m₆ : s₆.mem = (((s.mem.writeW (addr x SAVE) (s.gpr .ebx)).writeW (addr x (SAVE + 4)) (s.gpr .esi)).writeW
      (addr x (SAVE + 8)) (s.gpr .edi)).writeW (addr x (SAVE + 12)) (s.gpr .ebp) := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other .edi (by decide),
      u₁.other .ebp (by decide), u₁.other .esi (by decide), u₁.other .ebx (by decide)]
  have hS : ∀ d, SAVE ≤ d → d + 4 ≤ SAVE + 16 → (sub x SAVE 16).Contains (addr x d) 4 := fun d h₁ h₂ =>
    sub_contains (by simp only [SAVE]; omega_using [hfit]) h₁ h₂ (by decide)
  refine ⟨⟨by rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁, hfit,
      by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact h.wr, by decide, fun _ hW => absurd hW (by decide)⟩,
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide)],
    by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], ?_, ?_⟩
  · rw [m₆]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hS _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (hS _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (hS _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (hS _ (by decide) (by decide))
  · rw [m₆]
    have w : ∀ {m : Mem} {d e : Nat} {v : BitVec 32}, SAVE ≤ d → d + 4 ≤ SAVE + 16 → SAVE ≤ e →
        e + 4 ≤ SAVE + 16 → d + 4 ≤ e ∨ e + 4 ≤ d → wd (m.writeW (addr x e) v) x d = wd m x d := fun h₁ h₂ h₃ h₄ hne =>
      wd_write_ne _ _ (by simp only [SAVE] at *; omega_using [hfit, h₂]) (by simp only [SAVE] at *; omega_using [hfit, h₄])
        hne
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [w (by decide) (by decide) (by decide) (by decide) (by decide),
        w (by decide) (by decide) (by decide) (by decide) (by decide),
        w (by decide) (by decide) (by decide) (by decide) (by decide), wd_write_self]
    · rw [w (by decide) (by decide) (by decide) (by decide) (by decide),
        w (by decide) (by decide) (by decide) (by decide) (by decide), wd_write_self]
    · rw [w (by decide) (by decide) (by decide) (by decide) (by decide), wd_write_self]
    · rw [wd_write_self]

theorem entry_ok {s : State} {x : BitVec 32} (h : Entry s x) :
    WP isa (.block entry) s fun t =>
      Ctx 4096 x t ∧ t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [sub x SAVE 16, sub x AC 32] s.mem t.mem ∧ Saved x s.gpr t.mem ∧
      F t.mem x AC = F s.mem x Spec.X25519.Field32.aAt := by
  have hfit := h.fit
  rw [entry, WP.block_append_iff]
  refine WP.mono (save_ok h) fun t ⟨hc, esp, rd, wr, hf, hsv⟩ => ?_
  refine WP.mono (copy_ok hc below_AC below_aAt (.inr (.inl (by decide)))) fun u ⟨k, fu, eu⟩ => ?_
  have k₁ : ∀ d, SAVE ≤ d → d + 4 ≤ SAVE + 16 → wd u.mem x d = wd t.mem x d := fun d h₁ h₂ =>
    wd_frame1 fu hfit (by decide) (by simp only [SAVE] at h₂; omega) (.inr (by simp only [SAVE, AC] at *; omega))
  refine ⟨k.ctx hc, by rw [k.esp, esp], by rw [k.rd, rd], by rw [k.wr, wr],
    (hf.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..).trans
      (fu.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp),
    ⟨(k₁ _ (by decide) (by decide)).trans hsv.ebx, (k₁ _ (by decide) (by decide)).trans hsv.esi,
      (k₁ _ (by decide) (by decide)).trans hsv.edi, (k₁ _ (by decide) (by decide)).trans hsv.ebp⟩, ?_⟩
  simp only [F]
  rw [eu]
  exact congrArg VG.Proof.X25519.toFe (fe_frame1 hf hfit (by decide) (by decide) (.inl (by decide)))

theorem exit_ok {u : State} {x : BitVec 32} {g : Reg → BitVec 32} (hc : Ctx 4096 x u) (hsv : Saved x g u.mem) :
    WP isa (.block exit) u fun v => v.gpr .ebx = g .ebx ∧ v.gpr .esi = g .esi ∧ v.gpr .edi = g .edi ∧
      v.gpr .ebp = g .ebp ∧ v.gpr .esp = u.gpr .esp ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.mem = u.mem := by
  have hfit := hc.fit
  refine Wp.wp_mov fun u₁ v₁ => ?_
  have edx₁ : u₁.gpr .edx = x := by rw [v₁.gpr, hc.edi]
  have rin : ∀ d, d + 4 ≤ 4096 → InRegions (u₁.rd ++ u₁.wr) (addr x d) 4 := fun d hd =>
    ⟨_, List.mem_append_right _ (by rw [v₁.wr]; exact hc.wr), scR_contains hfit hd (by decide)⟩
  refine Wp.wp_ldm (B := x) (o := SAVE) edx₁ (rin _ (by decide)) fun u₂ v₂ => ?_
  refine Wp.wp_ldm (B := x) (o := SAVE + 4) (by rw [v₂.other _ (by decide)]; exact edx₁)
    (by rw [v₂.rd, v₂.wr]; exact rin _ (by decide)) fun u₃ v₃ => ?_
  refine Wp.wp_ldm (B := x) (o := SAVE + 12) (by rw [v₃.other _ (by decide), v₂.other _ (by decide)]; exact edx₁)
    (by rw [v₃.rd, v₃.wr, v₂.rd, v₂.wr]; exact rin _ (by decide)) fun u₄ v₄ => ?_
  refine Wp.wp_ldm (B := x) (o := SAVE + 8)
    (by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide)]; exact edx₁)
    (by rw [v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr]; exact rin _ (by decide)) fun u₅ v₅ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, by rw [v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd],
    by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr], by rw [v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]⟩
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem]; exact hsv.ebx
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem]; exact hsv.esi
  · rw [v₅.gpr, v₄.mem, v₃.mem, v₂.mem, v₁.mem]; exact hsv.edi
  · rw [v₅.other _ (by decide), v₄.gpr, v₃.mem, v₂.mem, v₁.mem]; exact hsv.ebp
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      v₁.other _ (by decide)]

/-- The regions the function writes: bytes 512 to 1023. -/
abbrev powW (x : BitVec 32) : List Region := [sub x 512 512]

theorem pow250Fn_ok {s : State} {x : BitVec 32} (h : Entry s x) :
    WP isa pow250Fn s fun t => (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame (powW x) s.mem t.mem ∧
      F t.mem x E1 = pw (F s.mem x Spec.X25519.Field32.aAt) (2 ^ 250 - 1) ∧
      F t.mem x E0 = pw (F s.mem x Spec.X25519.Field32.aAt) 11 := by
  have hfit := h.fit
  refine WP.seq (WP.mono (entry_ok h) fun t ⟨hc, esp, rd, wr, hf, hsv, ha⟩ => ?_)
  refine WP.seq (WP.mono (chain_spec x t hc) fun u ⟨ku, eu⟩ => ?_)
  have hsv' : Saved x s.gpr u.mem := by
    have k : ∀ d, SAVE ≤ d → d + 4 ≤ SAVE + 16 → wd u.mem x d = wd t.mem x d := fun d h₁ h₂ =>
      wd_frame1 ku.frame hfit (by decide) (by simp only [SAVE] at h₂; omega) (.inr (by simp only [SAVE] at h₁; omega))
    exact ⟨(k _ (by decide) (by decide)).trans hsv.ebx, (k _ (by decide) (by decide)).trans hsv.esi,
      (k _ (by decide) (by decide)).trans hsv.edi, (k _ (by decide) (by decide)).trans hsv.ebp⟩
  refine WP.mono (exit_ok (ku.ctx hc) hsv') fun v ⟨rb, rs, ri, rp, re, rr, rw', rm⟩ => ?_
  obtain ⟨v1, v0⟩ := chainEnv_eval (cenv t.mem x)
  have e1 := congrFun eu 1
  have e0 := congrFun eu 0
  have hz : cenv t.mem x 4 = F s.mem x Spec.X25519.Field32.aAt := ha
  refine ⟨fun r hr => ?_, by rw [rr, ku.rd, rd], by rw [rw', ku.wr, wr], ?_, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rb
    · exact rs
    · exact ri
    · exact rp
    · rw [re, ku.esp, esp]
  · rw [rm]
    have sub512 : ∀ r ∈ [sub x SAVE 16, sub x AC 32], ∃ r' ∈ powW x, Region.Sub r r' := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact ⟨_, List.mem_singleton_self _, sub_sub hfit (by decide) (by decide) (by decide)⟩
    refine (hf.sub sub512).trans (ku.frame.sub fun r hr => ?_)
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, sub_sub hfit (Nat.le_refl _) (by decide) (by decide)⟩
  · rw [rm]
    change cenv u.mem x 1 = _
    rw [e1, v1, hz, chainF_eq]
  · rw [rm]
    change cenv u.mem x 0 = _
    rw [e0, v0, hz, chainF_eq]

end VG.Proof.X25519.X86.Field32
