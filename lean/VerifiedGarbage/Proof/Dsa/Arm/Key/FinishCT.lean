module

public import VerifiedGarbage.Proof.Dsa.Arm.Key.Finish
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Two
import VerifiedGarbage.Proof.Dsa.Arm.Key.Body
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.Finish
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.Two
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.Body
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Key generation's exit leaks only the status (32-bit ARM)

`finish` branches on the overall status, and writes through the public `out`
and `used` pointers.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp op2_imm eval_eq eval_ne)

/-- At the end: the frame's slots, and the overall status `p.2`. -/
def FinAt (p : Pub × Nat) : State → Prop := At (fun s₀ t => RFin s₀ t ∧ (rResult s₀).status = p.2) p.1

/-! ## The end -/

/-- Test the overall status. -/
theorem finTest_ok {s₀ t : State} (A : KeyABI s₀) (F : RFin s₀ t) :
    WP isa (.block [ld .r0 oStatus, .cmp .r0 (.imm 1)]) t fun u =>
      RReady s₀ u ∧ Saved s₀ u.mem ∧ u.z = decide ((rResult s₀).status = 1) := by
  have hR := rResult_status_le A
  refine wp_ld F.ready (by decide) fun t₁ u₁ => wp_cmp (op2_imm (by decide)) fun t₂ f₂ z₂ => WP.block_nil ?_
  rw [u₁.gpr, F.status, one_beq (by omega)] at z₂
  exact ⟨(F.ready.upd u₁).fupd f₂, by rw [f₂.mem, u₁.mem]; exact F.saved, z₂⟩

/-- Ready, with public data `p.1`. -/
def ReadyAt (p : Pub × Nat) : State → Prop := At (fun s₀ t => RReady s₀ t ∧ Saved s₀ t.mem) p.1

/-- The output's address and length. -/
theorem zeroHead_ok {s₀ t : State} (h : RReady s₀ t) (sv : Saved s₀ t.mem) :
    WP isa (.block [ld .r1 oOut, ld .r2 oOutLen, .mov .r0 (.imm 0)]) t fun u =>
      u.gpr .r1 = s₀.gpr .r0 ∧ u.gpr .r2 = s₀.gpr .r1 := by
  refine wp_ld h (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
    VG.Proof.X25519.Arm.wp_mov (op2_imm (by decide)) fun t₃ u₃ => WP.block_nil ⟨?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, sv.2.1]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, sv.2.2.1]

theorem zeroOut_ct : RelCT isa (Two fun p s => ReadyAt p s ∧ isa.eval .ne s = some true) zeroOut
    fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_piece (Ψ := fun p => At (fun s₀ t => t.gpr .r1 = s₀.gpr .r0 ∧ t.gpr .r2 = s₀.gpr .r1) p.1)
    [.r11] (pins_at' (P := fun _ s₀ t => RReady s₀ t ∧ Saved s₀ t.mem) Prod.fst fun _ _ _ h => h.1)
    (by taint_decide) fun p t ⟨⟨s₀, A, e, h, sv⟩, _⟩ => WP.mono (zeroHead_ok h sv) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine two_taint [.r1, .r2] (fun p t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, x₁, c₁⟩ := h₁
  obtain ⟨s₂, _, e₂, x₂, c₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [x₁, x₂, pub_r0 e]
  · rw [c₁, c₂, pub_r1 e]

/-- The nonce cleared, and the address of `used`. -/
theorem finPrefix_ok {s₀ t : State} (h : RReady s₀ t) (sv : Saved s₀ t.mem) :
    WP isa (.block (clearNonce ++ ([ld .r4 oUsedPtr] : List Instr))) t fun u =>
      RReady s₀ u ∧ u.gpr .r4 = s₀.gpr .r2 := by
  refine clearNonce_ok h fun t₁ h₁ m₁ _ _ => ?_
  have o₁ : Outs (rBase s₀) [(oNonce, 32)] t.mem t₁.mem := by
    rw [m₁]; exact Outs.of_outside (clearMem_outside _ _ 8 (by decide)) (List.mem_singleton_self _)
  have sv₁ : Saved s₀ t₁.mem := sv.of_outs o₁ (by decide)
  exact wp_ld h₁ (by decide) fun t₂ u₂ => WP.block_nil ⟨h₁.upd u₂, by rw [u₂.gpr]; exact sv₁.2.2.2.1⟩

theorem finalBlock_ct : RelCT isa (Two ReadyAt) (.block (clearNonce ++ finalList)) fun _ _ => True := by
  show RelCT isa _ (.block ((clearNonce ++ [ld .r4 oUsedPtr]) ++
    [ld .r0 oUsed, .str .r0 .r4 0, .mov .r0 (.imm 0), .str .r0 .r4 4, ld .r0 oStatus,
      ld .r4 0, ld .r5 4, ld .r6 8, ld .r7 12, ld .r8 16, ld .r9 20, ld .r10 24, ld .lr 32, ld .r11 28])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p => At (fun s₀ t => RReady s₀ t ∧ t.gpr .r4 = s₀.gpr .r2) p.1)
    [.r11] (pins_at (P := fun _ s₀ t => RReady s₀ t ∧ Saved s₀ t.mem) Prod.fst fun _ _ _ h => h.1)
    (by taint_decide) fun p t ⟨s₀, A, e, h, sv⟩ => WP.mono (finPrefix_ok h sv) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine two_taint [.r11, .r4] (fun p t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, r₁, d₁⟩ := h₁
  obtain ⟨s₂, _, e₂, r₂, d₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact r11_of_rf r₁.rf (pub_rBase e ▸ r₂.rf)
  · rw [d₁, d₂, pub_r2 e]

theorem finish_ct : RelCT isa (Two FinAt) finish fun _ _ => True := by
  unfold finish
  rw [finishBlock_eq]
  refine RelCT.seq (two_piece (Ψ := fun (p : Pub × Nat) => At (fun s₀ t => RReady s₀ t ∧ Saved s₀ t.mem ∧
      t.z = decide (p.2 = 1)) p.1) [.r11]
    (pins_at (P := fun p s₀ t => RFin s₀ t ∧ (rResult s₀).status = p.2) Prod.fst fun _ _ _ h => h.1.ready)
    (by taint_decide) fun p t ⟨s₀, A, e, Fi, st⟩ => WP.mono (finTest_ok A Fi)
      fun u ⟨h, sv, z⟩ => ⟨s₀, A, e, h, sv, by rw [z, st]⟩) ?_
  refine RelCT.seq (R := Two ReadyAt) (two_ite (fun p t₁ t₂ ⟨s₁, _, e₁, _, _, z₁⟩ ⟨s₂, _, e₂, _, _, z₂⟩ => by
    rw [eval_ne, eval_ne, z₁, z₂]) ?_ ?_) finalBlock_ct
  · exact two_post (Ψ := ReadyAt) (two_map id (fun p t ⟨⟨s₀, A, e, h, sv, _⟩, hb⟩ => ⟨⟨s₀, A, e, h, sv⟩, hb⟩)
      zeroOut_ct) fun p t ⟨⟨s₀, A, e, h, sv, _⟩, _⟩ => WP.mono (zeroOut_ok A h sv)
        fun u ⟨hv, fv, _, _⟩ => ⟨s₀, A, e, hv, sv.of_slots fun d _ hd => apart_slot fv A.stackOut hd⟩
  · exact two_post (Ψ := ReadyAt) (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide))
      fun p t ⟨⟨s₀, A, e, h, sv, _⟩, _⟩ => WP.block_nil ⟨s₀, A, e, h, sv⟩

end VG.Proof.Dsa.Arm.Key
