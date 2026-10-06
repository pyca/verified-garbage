import VerifiedGarbage.Proof.AesOcb.X86.LNtz

/-!
# AES-OCB on x86: `L_$`, `L_0` and the checksum (`setup`)

Untrusted: everything here is checked by Lean. `setup` doubles `L_*` (bytes
240–255 of the key context) to `L_$` at `W + ldO`, doubles that to `L_0` at
`W + l0O`, and zeroes the checksum at `W + ckO` (`setup_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem double lAt lDollar ctxLstar)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq runBlock_app_of)

theorem zero4_fold (m : Mem) (W : BitVec 32) (d : Nat) :
    (((m.writeW (w64 W + BitVec.ofNat 64 d) (BitVec.ofNat 32 0)).writeW (w64 W + BitVec.ofNat 64 (d + 4))
      (BitVec.ofNat 32 0)).writeW (w64 W + BitVec.ofNat 64 (d + 8)) (BitVec.ofNat 32 0)).writeW
      (w64 W + BitVec.ofNat 64 (d + 12)) (BitVec.ofNat 32 0) = Proof.Cmac.zero4 m (w64 W + BitVec.ofNat 64 d) := by
  simp only [Proof.Cmac.zero4, Proof.Cmac.store4, Proof.AesGcm.X86.add_ofNat_assoc]; rfl

/-- A block of `W` below 128, within `wA`. -/
theorem frame_wA {p : Prm} {d : Nat} (h : d + 16 ≤ 128) {m m' : Mem}
    (hf : Frame [⟨w64 p.W + BitVec.ofNat 64 d, 16⟩] m m') : Frame [wA p.W] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ h⟩

/-- A zeroed block is zero. -/
theorem blockAtMem_zero4 (m : Mem) (c : Addr) : blockAtMem (Proof.Cmac.zero4 m c) c = 0 := by
  rw [blockAtMem, Proof.Cmac.zero4_bytes]; decide

/-- What `setup` leaves. -/
structure SetupPost (p : Prm) (s s' : State) : Prop where
  frame : Frame [wA p.W] s.mem s'.mem
  ld : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem (w64 p.K))
  l0 : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (w64 p.K)) 0
  ck : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem setup_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    ∃ s', runBlock isa setup s = some s' ∧ SetupPost p s s' := by
  obtain ⟨s₁, run₁, m₁, b₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .ebx (slot ctxO)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .ebx = p.K ∧ (∀ r, r ≠ .ebx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    have hc := E.slots.ctx
    simp only [slotv_eq] at hc
    exact ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hc], by gmems [], by gregs [hc], fun r h => by gregs [h],
      by gmems [], by gmems []⟩
  have E₁ : Env p s₁ := E.keep (by rw [g₁ _ (by decide)]) (by rw [g₁ _ (by decide)]) rd₁ wr₁ m₁
  obtain ⟨s₂, run₂, m₂, g₂, rd₂, wr₂⟩ := dblK_ok L E₁ b₁ (s := 240) (d := ldO) (by decide) (by decide)
  have E₂ : Env p s₂ := E₁.mut L (by rw [g₂ _ (by decide) (by decide) (by decide), E₁.ebp])
    (by rw [g₂ _ (by decide) (by decide) (by decide), E₁.esp]) rd₂ wr₂
    (frame_toMut (by rw [m₂]; exact dblMem_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := dblW_ok L E₂ (s := ldO) (d := l0O) (by decide) (by decide)
    (.inr (.inl (by decide)))
  have E₃ : Env p s₃ := E₂.mut L (by rw [g₃ _ (by decide) (by decide) (by decide), E₂.ebp])
    (by rw [g₃ _ (by decide) (by decide) (by decide), E₂.esp]) rd₃ wr₃
    (frame_toMut (by rw [m₃]; exact dblMem_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa (zero4 ckO) s₃ = some s₄ ∧
      s₄.mem = Proof.Cmac.zero4 s₃.mem (w64 p.W + BitVec.ofNat 64 ckO) ∧
      (∀ r, r ≠ .eax → s₄.gpr r = s₃.gpr r) ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr :=
    ⟨_, by grun [zero4, E₃.ebp, L.aW, E₃.perm.wW], by gmems []; exact zero4_fold _ _ _, fun r h => by gregs [h],
      by gmems [], by gmems []⟩
  refine ⟨s₄, runBlock_app_of (runBlock_app_of (runBlock_app_of run₁ run₂) run₃) run₄, ?_⟩
  have f₄ : Frame [wA p.W] s₃.mem s₄.mem := by rw [m₄]; exact frame_wA (by decide) (Proof.Cmac.frame_store4 _ _ _ _ _)
  have hd : ∀ {d : Nat}, d + 16 ≤ ckO ∨ ckO + 16 ≤ d → d + 16 ≤ 2560 →
      blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 d) :=
    fun h h' => by
      rw [m₄]
      exact Proof.Ocb.blockAtMem_frame (Proof.Cmac.frame_store4 _ _ _ _ _) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w h h' (by decide)
  have hld₂ : blockAtMem s₂.mem (w64 p.W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem (w64 p.K)) := by
    rw [m₂, dblMem_block, m₁]; rfl
  have hl0 : blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem (w64 p.K)) := by
    rw [m₃, Proof.Ocb.blockAtMem_frame (dblMem_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (by decide) (by decide) (by decide), hld₂]
  refine ⟨?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · have f₂ : Frame [wA p.W] s.mem s₂.mem := by
      rw [m₂, m₁]; exact frame_wA (by decide) (dblMem_frame _ _ _ _ _)
    have f₃ : Frame [wA p.W] s₂.mem s₃.mem := by rw [m₃]; exact frame_wA (by decide) (dblMem_frame _ _ _ _ _)
    exact (f₂.trans f₃).trans f₄
  · rw [hd (by decide) (by decide), hl0]
  · rw [hd (by decide) (by decide), m₃, dblMem_block, hld₂]; rfl
  · rw [m₄]; exact blockAtMem_zero4 _ _
  · rw [g₄ r h₁, g₃ r h₁ h₂ h₃, g₂ r h₁ h₂ h₃, g₁ r h₄]

end VG.Proof.AesOcb.X86
