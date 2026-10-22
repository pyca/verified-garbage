module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Callee
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Contract

import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Rel
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Save
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Callee
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Contract
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Rel
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Env
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Save
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.AArch64.Env

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_init` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/AArch64/InitCT.lean`): the code around the calls by the taint
analysis, from the public arguments and the registers the correctness proof
pins (`init1_ok`, `init2_ok`); the calls by their callees' proofs, with the
arguments those proofs give.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (mov ptr imm tO save)
open VG.Proof.AesGcm.AArch64

/-- The block before the call of `vg_sm4_expand_key`. -/
theorem init1_ok {s : State} {K Ctx W : Addr} (hK : s.gpr .x0 = K) (hCtx : s.gpr .x1 = Ctx)
    (hW : s.gpr .x2 = W) (hsp : 3264 ≤ s.sp.toNat) (hrd : s.rd = [⟨K, 16⟩])
    (hwr : s.wr = [⟨Ctx, 256⟩, ⟨W, 768⟩]) (d_kc : (⟨K, 16⟩ : Region).Disjoint ⟨Ctx, 256⟩)
    (sK : (stk s.sp).Disjoint ⟨K, 16⟩) (sC : (stk s.sp).Disjoint ⟨Ctx, 256⟩)
    (fK : K.toNat + 16 ≤ 2 ^ 64) (fC : Ctx.toNat + 256 ≤ 2 ^ 64) :
    WP isa (.block initSeg1) s fun s₂ => KeyCall s₂ K Ctx ∧ s₂.gpr .x19 = W ∧
      s₂.gpr .x21 = Ctx ∧ s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  have pW : Covers [⟨W, 768⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have pK : Covers [⟨K, 16⟩] (s.rd ++ s.wr) := by rw [hrd]; exact covers_of_mem (by simp)
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x2 hW pW
  obtain ⟨s₂, run₂, x19₂, x21₂, x0₂, x1₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x2, mov .x21 .x1] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x21 = Ctx ∧ s₂.gpr .x0 = K ∧ s₂.gpr .x1 = Ctx ∧
      s₂.sp = s₁.sp ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hCtx]
    · simp [gpr_write, g₁, hK]
    · simp [gpr_write, g₁, hCtx]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  have rd₂' : s₂.rd = s.rd := rd₂.trans rd₁
  have wr₂' : s₂.wr = s.wr := wr₂.trans wr₁
  have sp₂' : s₂.sp = s.sp := sp₂.trans sp₁
  refine ⟨⟨x0₂, x1₂, by rw [sp₂']; exact hsp, fK, by omega, d_kc.sub_right (Region.sub_prefix (by decide)),
      by rw [sp₂']; exact sK, by rw [sp₂']; exact sC.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩,
    x19₂, x21₂, sp₂', rd₂', wr₂'⟩
  · rw [rd₂', wr₂']
    exact covers_cons pK (covers_left (covers_prefix pC (by decide)))
  · rw [wr₂']; exact covers_prefix pC (by decide)

/-- The block before the call of `vg_sm4_ctr32`. -/
theorem init2_ok {s : State} {Ctx W : Addr} (h19 : s.gpr .x19 = W) (h21 : s.gpr .x21 = Ctx)
    (hsp : 3264 ≤ s.sp.toNat) (pC : Covers [⟨Ctx, 256⟩] s.wr) (pW : Covers [⟨W, 768⟩] s.wr)
    (d_cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 768⟩) (sC : (stk s.sp).Disjoint ⟨Ctx, 256⟩)
    (sW : (stk s.sp).Disjoint ⟨W, 768⟩) (fC : Ctx.toNat + 256 ≤ 2 ^ 64) (fW : W.toNat + 768 ≤ 2 ^ 64) :
    WP isa (.block initSeg2) s fun s₄ =>
      CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) 1 ∧
      s₄.gpr .x19 = W ∧ s₄.gpr .x21 = Ctx ∧ s₄.sp = s.sp := by
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := in_off pW (show 96 + 8 ≤ 768 by decide) (by decide)
  have w₄ := in_off pW (show 104 + 8 ≤ 768 by decide) (by decide)
  obtain ⟨s₄, run₄, x0₄, x1₄, x2₄, x3₄, og₄, sp₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa initSeg2 s = some s₄ ∧
      s₄.gpr .x0 = Ctx ∧ s₄.gpr .x1 = W + BitVec.ofNat 64 96 ∧ s₄.gpr .x2 = Ctx + BitVec.ofNat 64 240 ∧
      s₄.gpr .x3 = BitVec.ofNat 64 1 ∧ Others [.x9, .x0, .x1, .x2, .x3] s s₄ ∧
      s₄.sp = s.sp ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr := by
    refine ⟨_, by simp only [initSeg2]; arun [h19, h21, w₁, w₂, w₃, w₄], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp [gpr_write, h21]
    · simp [gpr_write, h19]
    · simp [gpr_write, h21]
    · simp [gpr_write]
  refine WP.of_runBlock ⟨s₄, run₄, ?_, by rw [og₄ _ (by decide), h19], by rw [og₄ _ (by decide), h21], sp₄⟩
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 768 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ he)
  have dK0 : (⟨Ctx, 128⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega)
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄]; exact pC
  have pW' : Covers [⟨W, 768⟩] s₄.wr := by rw [wr₄]; exact pW
  refine ⟨x0₄, x1₄, x2₄, x3₄, by rw [sp₄]; exact hsp, by decide, ?_, by omega, ?_,
    ?_, dK0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (W.toNat + 96 % 2 ^ 64) (2 ^ 64); omega
  · simpa using dCW 0 128 (by decide) 96 16 (by decide)
  · exact (dCW 240 16 (by decide) 96 16 (by decide)).symm
  · rw [sp₄]; exact sC.sub_right (Region.sub_prefix (by decide))
  · rw [sp₄]; exact sW.sub_right (Offset.sub_base W (by decide))
  · rw [sp₄]; exact sC.sub_right (Offset.sub_base Ctx (by decide))
  · exact covers_cons (covers_left (covers_prefix pC' (by decide))) (covers_cons
      (covers_left (covers_off pW' (by decide) (by decide)))
      (covers_left (covers_off pC' (by decide) (by decide))))
  · exact covers_cons (covers_off pW' (by decide) (by decide)) (covers_off pC' (by decide) (by decide))

theorem init_ct : ConstantTime isa initAArch64.pre initAArch64.pub init := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, qsp⟩ := hq
  simp only [initAArch64] at h₁ h₂
  rw [← q0, ← q1, ← q2, ← qsp] at h₂
  obtain ⟨hsp, hrd₁, hwr₁, d_kc, -, d_cs, sK, sC, sW, fK, fC, fW⟩ := h₁
  obtain ⟨-, hrd₂, hwr₂, -⟩ := h₂
  generalize hK : σ₁.gpr .x0 = K at *
  generalize hCtx : σ₁.gpr .x1 = Ctx at *
  generalize hW : σ₁.gpr .x2 = W at *
  refine rel_seq (rel_taint [.x0, .x1, .x2] qsp (by agree_tac [hK, hCtx, hW, ← q0, ← q1, ← q2])
      ⟨_, by taint_decide⟩)
    (init1_ok hK hCtx hW hsp hrd₁ hwr₁ d_kc sK sC fK fC)
    (init1_ok q0.symm q1.symm q2.symm (by rw [← qsp]; exact hsp) hrd₂ hwr₂ d_kc (by rw [← qsp]; exact sK)
      (by rw [← qsp]; exact sC) fK fC)
    fun τ₁ τ₂ ⟨k₁, x19₁, x21₁, sp₁, rd₁, wr₁⟩ ⟨k₂, x19₂, x21₂, sp₂, rd₂, wr₂⟩ => ?_
  refine rel_seq (rel_key k₁ k₂ (by rw [sp₁, sp₂, qsp])) (key_call k₁) (key_call k₂)
    fun τ₁' τ₂' g₁ g₂ => ?_
  have pv : ∀ {σ τ τ' : State}, σ.wr = [⟨Ctx, 256⟩, ⟨W, 768⟩] → τ.wr = σ.wr → τ.sp = σ.sp →
      σ.sp = σ₁.sp → KeyPost τ K Ctx τ' → τ.gpr .x19 = W → τ.gpr .x21 = Ctx →
      WP isa (.block initSeg2) τ' fun s₄ => CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) 1 ∧
        s₄.gpr .x19 = W ∧ s₄.gpr .x21 = Ctx ∧ s₄.sp = τ'.sp :=
    fun hwr wr sp sp' g h19 h21 => init2_ok (by rw [g.saved .x19 (by decide) (by decide), h19])
      (by rw [g.saved .x21 (by decide) (by decide), h21]) (by rw [g.sp, sp, sp']; exact hsp)
      (by rw [g.wr, wr, hwr]; exact covers_of_mem (by simp))
      (by rw [g.wr, wr, hwr]; exact covers_of_mem (by simp)) d_cs (by rw [g.sp, sp, sp']; exact sC)
      (by rw [g.sp, sp, sp']; exact sW) fC fW
  refine rel_seq (rel_taint [.x19, .x21] (by rw [g₁.sp, g₂.sp, sp₁, sp₂, qsp])
      (by agree_tac [g₁.saved .x19 (by decide) (by decide), g₂.saved .x19 (by decide) (by decide),
        g₁.saved .x21 (by decide) (by decide), g₂.saved .x21 (by decide) (by decide), x19₁, x19₂, x21₁, x21₂])
      ⟨_, by taint_decide⟩)
    (pv hwr₁ wr₁ sp₁ rfl g₁ x19₁ x21₁) (pv hwr₂ wr₂ sp₂ qsp.symm g₂ x19₂ x21₂)
    fun τ₁ τ₂ ⟨c₁, y₁, z₁, s₁'⟩ ⟨c₂, y₂, z₂, s₂'⟩ => ?_
  refine rel_seq (rel_ctr c₁ c₂ (by rw [s₁', s₂', g₁.sp, g₂.sp, sp₁, sp₂, qsp]))
    (ctr_call c₁) (ctr_call c₂) fun τ₁ τ₂ e₁ e₂ => ?_
  exact rel_taint [.x19, .x21] (by rw [e₁.sp, e₂.sp, s₁', s₂', g₁.sp, g₂.sp, sp₁, sp₂, qsp])
    (by agree_tac [e₁.saved .x19 (by decide) (by decide), e₂.saved .x19 (by decide) (by decide), y₁, y₂,
      e₁.saved .x21 (by decide) (by decide), e₂.saved .x21 (by decide) (by decide), z₁, z₂]) ⟨_, by taint_decide⟩

end VG.Proof.Sm4Gcm.AArch64
