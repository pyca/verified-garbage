module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTPoint
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Exit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPreserves
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPreserves
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Outputs
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Outputs
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Policy
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Policy
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ZeroOutput
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ZeroOutput

/-! Rejections and incomplete searches clear outputs on public addresses
and public-length schedules; scalar and output bytes do not affect timing. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm

def KeyZeroCT (j : Nat) (p : KeyPublic) (s : State) : Prop :=
  KeyAny p s ∧ s.gpr .r0 = (if j = 5 then p.xp else p.yp) ∧ s.gpr .lr = BitVec.ofNat 32 p.len

private theorem zero_header (j : Nat) (which : j = 5 ∨ j = 6) (p : KeyPublic) (s : State)
    (h : KeyAny p s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 j, VG.Impl.Ffdh.Arm.KeySearch.ldf .lr 2,
      .mov .r2 (.imm 0)]) s (KeyZeroCT j p) := by
  obtain ⟨original, used, keys, scalars, live⟩ := h
  have pointer : lowWord s.mem p.control j = (if j = 5 then p.xp else p.yp) := by
    rcases which with rfl | rfl <;> exact live.header (by simp [KeyPublic.headers])
  have slot : j < 16 := by rcases which with rfl | rfl <;> decide
  refine WP.mono (zeroOutputArgs_ok s (n := p.len) live.controller slot pointer
    (live.header (by simp [KeyPublic.headers]))) ?_
  rintro t ⟨⟨ptr, count, _, mem⟩, rest⟩
  exact ⟨⟨original, _, _, _, live.keep rest mem⟩, ptr, count⟩

private theorem zero_ct (j : Nat) (which : j = 5 ∨ j = 6) :
    RelCT isa (Two KeyAny) (VG.Impl.Ffdh.Arm.KeySearch.zeroOutput j) (fun _ _ => True) := by
  rcases which with rfl | rfl <;> unfold VG.Impl.Ffdh.Arm.KeySearch.zeroOutput
  all_goals
    refine RelCT.seq (two_piece [.r4] key_any_pins (by taint_decide) (zero_header _ (by decide))) ?_
    exact two_taint [.r0, .lr] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁.2.1.trans h₂.2.1.symm
      · exact h₁.2.2.trans h₂.2.2.symm) (by taint_decide)

private theorem zero_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (VG.Impl.Ffdh.Arm.KeySearch.zeroOutput 5) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, live⟩ := h
  refine WP.mono (zeroOutput_ok s (n := p.len) (dst := p.xp) live.controller (by decide : 5 < 16)
    (by have := live.input.bounds.minLength; omega) (by have := live.input.bounds.maxLength; omega)
    (live.header (by simp [KeyPublic.headers])) (live.header (by simp [KeyPublic.headers])) live.x_buffer) ?_
  rintro t ⟨_, frame, rest⟩
  exact ⟨original, _, _, _, live.restore rest.rd rest.wr rest.sp
    (fun r hr => rest.gpr r (by revert r hr; decide)) (frame.mono (by simp [callChanges]))⟩

theorem zero_outputs_ct : RelCT isa (Two KeyAny) VG.Impl.Ffdh.Arm.KeySearch.zeroOutputs (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.zeroOutputs
  exact RelCT.seq (two_post (zero_ct 5 (.inl rfl)) zero_ready) (zero_ct 6 (.inr rfl))

private theorem terminal_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.terminal 3)) s (KeyAny p) := by
  obtain ⟨original, _, _, _, live⟩ := h
  exact WP.mono (live.terminal (status := 3) (.inr rfl)) fun _ ⟨ready, _⟩ => ⟨original, _, _, _, ready⟩

theorem exhausted_ct : RelCT isa (Two KeyAny) VG.Impl.Ffdh.Arm.KeySearch.exhausted (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.exhausted
  exact RelCT.seq (two_piece [.r4] key_any_pins (by taint_decide) terminal_ready) zero_outputs_ct

private theorem request_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r10 2, .mov .r11 (.imm 0),
      VG.Impl.Ffdh.Arm.KeySearch.stf .r10 3, .str .r11 .r4 28,
      VG.Impl.Ffdh.Arm.KeySearch.stf .r11 14]) s (KeyAny p) := by
  obtain ⟨original, _, _, _, live⟩ := h
  exact WP.mono live.request_block fun _ ⟨ready, _⟩ => ⟨original, _, _, _, ready⟩

theorem request_ct : RelCT isa (Two KeyAny) VG.Impl.Ffdh.Arm.KeySearch.request (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.request
  exact RelCT.seq (two_piece [.r4] key_any_pins (by taint_decide) request_ready) zero_outputs_ct

theorem accepted_ct : RelCT isa (Two KeyAny) (.block (VG.Impl.Ffdh.Arm.KeySearch.terminal 1)) (fun _ _ => True) :=
  two_taint [.r4] key_any_pins (by taint_decide)

theorem rejected_scalar_ct : RelCT isa (Two KeyAny) (.block VG.Impl.Ffdh.Arm.KeySearch.rejectedScalar) (fun _ _ => True) :=
  two_taint [.r4] key_any_pins (by taint_decide)

theorem rejected_public_ct : RelCT isa (Two KeyAny) (.block VG.Impl.Ffdh.Arm.KeySearch.rejectedPublic) (fun _ _ => True) :=
  two_taint [.r4] key_any_pins (by taint_decide)

end VG.Proof.Ffdh.Arm.KeySearch
