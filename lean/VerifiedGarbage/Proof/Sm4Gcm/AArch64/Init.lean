module
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Callee
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Contract
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Save

import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Crypt
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Flush
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.AesGcm.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_init`

Untrusted: everything here is checked by Lean. The key schedule from
`vg_sm4_expand_key` in the context's first 128 bytes, then the hash subkey
`CIPH_K(0¹²⁸)` at byte 240 from `vg_sm4_ctr32` over a zero block with a zero
counter block (`init_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (mov ptr imm tO scrO save saved restore)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Spec.Sm4.Gcm (KeyRepr)
open VG.Spec.Gcm (ctxH)

/-- SM4's block at `p` is the 16 bytes there. -/
theorem sm4BlockAt_eq (m : Mem) (p : Addr) :
    Spec.Sm4.blockAt m p = Vector.ofFn fun i : Fin 16 => (bytesAt m p 16).getD i.val 0 := by
  unfold Spec.Sm4.blockAt
  congr 1
  funext i
  simp [bytesAt, i.isLt]

/-- `vg_sm4_gcm_init`. -/
theorem init_wp {s : State} (hp : initAArch64.pre s) :
    WP isa init s fun s' => GprAbi s s' ∧ initAArch64.post s s' := by
  simp only [initAArch64] at hp ⊢
  obtain ⟨hsp, hrd, hwr, d_kc, d_ks, d_cs, sK, sC, sW, fK, fC, fW⟩ := hp
  generalize hK : s.gpr .x0 = K at *
  generalize hCtx : s.gpr .x1 = Ctx at *
  generalize hW : s.gpr .x2 = W at *
  have pW : Covers [⟨W, 768⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have pK : Covers [⟨K, 16⟩] (s.rd ++ s.wr) := by rw [hrd]; exact covers_of_mem (by simp)
  -- The registers saved, the context and `W` to `x21` and `x19`.
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x2 hW pW
  obtain ⟨s₂, run₂, x19₂, x21₂, x0₂, x1₂, og₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x2, mov .x21 .x1] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x21 = Ctx ∧ s₂.gpr .x0 = K ∧ s₂.gpr .x1 = Ctx ∧
      Others [.x19, .x21] s₁ s₂ ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hCtx]
    · simp [gpr_write, g₁, hK]
    · simp [gpr_write, g₁, hCtx]
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  have rd₂' : s₂.rd = s.rd := rd₂.trans rd₁
  have wr₂' : s₂.wr = s.wr := wr₂.trans wr₁
  have sp₂' : s₂.sp = s.sp := sp₂.trans sp₁
  -- The key schedule.
  have kc : KeyCall s₂ K Ctx := by
    refine ⟨x0₂, x1₂, by rw [sp₂']; exact hsp, fK, by omega_arith, d_kc.sub_right (Region.sub_prefix (by decide)),
      by rw [sp₂']; exact sK, by rw [sp₂']; exact sC.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
    · rw [rd₂', wr₂']
      exact covers_cons pK (covers_left (covers_prefix pC (by decide)))
    · rw [wr₂']; exact covers_prefix pC (by decide)
  refine WP.seq (WP.mono (key_call kc) fun s₃ g => ?_)
  have g19 : s₃.gpr .x19 = W := by rw [g.saved .x19 (by decide) (by decide), x19₂]
  have g21 : s₃.gpr .x21 = Ctx := by rw [g.saved .x21 (by decide) (by decide), x21₂]
  have rd₃ : s₃.rd = s.rd := g.rd.trans rd₂'
  have wr₃ : s₃.wr = s.wr := g.wr.trans wr₂'
  have sp₃ : s₃.sp = s.sp := g.sp.trans sp₂'
  have gf := g.frame
  rw [sp₂'] at gf
  -- A zero block at the context's `H` and a zero counter block in `T`.
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := in_off pW (show 96 + 8 ≤ 768 by decide) (by decide)
  have w₄ := in_off pW (show 104 + 8 ≤ 768 by decide) (by decide)
  rw [← wr₃] at w₁ w₂ w₃ w₄
  obtain ⟨s₄, run₄, hm₄, x0₄, x1₄, x2₄, x3₄, og₄, sp₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa initSeg2 s₃ = some s₄ ∧
      s₄.mem = (((s₃.mem.writeW (Ctx + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (Ctx + BitVec.ofNat 64 248) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 104) (0 : BitVec 64) ∧
      s₄.gpr .x0 = Ctx ∧ s₄.gpr .x1 = W + BitVec.ofNat 64 96 ∧ s₄.gpr .x2 = Ctx + BitVec.ofNat 64 240 ∧
      s₄.gpr .x3 = BitVec.ofNat 64 1 ∧ Others [.x9, .x0, .x1, .x2, .x3] s₃ s₄ ∧
      s₄.sp = s₃.sp ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    refine ⟨_, by simp only [initSeg2]; arun [g19, g21, w₁, w₂, w₃, w₄], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, g21]
    · simp [gpr_write, g19]
    · simp [gpr_write, g21]
    · simp [gpr_write]
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have rd₄' : s₄.rd = s.rd := rd₄.trans rd₃
  have wr₄' : s₄.wr = s.wr := wr₄.trans wr₃
  have sp₄' : s₄.sp = s.sp := sp₄.trans sp₃
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 768 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ he)
  have dK0 : (⟨Ctx, 128⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega_arith)
  have e248 : Ctx + BitVec.ofNat 64 248 = Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 :=
    (add_ofNat_assoc _ 240 8).symm
  have e104 : W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 :=
    (add_ofNat_assoc _ 96 8).symm
  rw [e248, e104] at hm₄
  have f₄ : Frame [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact ((Proof.Cmac.frame_store2 _ _ _).mono (by simp)).trans ((Proof.Cmac.frame_store2 _ _ _).mono (by simp))
  have hT₄ : blockAt s₄.mem (W + BitVec.ofNat 64 96) = 0 := by
    rw [blockAt, hm₄, zeroT_bytes]; decide
  have hD₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = 0 := by
    rw [blockAt, hm₄, bytesAt_frame (Proof.Cmac.frame_store2 _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dCW 240 16 (by decide) 96 16 (by decide)) (by decide),
      zeroT_bytes]
    decide
  have fsv : Frame [savedR W] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  -- The key, as the callee read it, and the schedule.
  have hKey : Spec.Sm4.blockAt s₂.mem K = Vector.ofFn fun i : Fin 16 => (bytesAt s.mem K 16).getD i.val 0 := by
    rw [sm4BlockAt_eq, m₂, bytesAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d_ks.sub_right (Offset.sub_base W (by decide)))
      (by decide)]
  have hk₄ : Spec.Sm4.scheduleAt s₄.mem Ctx =
      Spec.Sm4.expandKey (Vector.ofFn fun i : Fin 16 => (bytesAt s.mem K 16).getD i.val 0) := by
    rw [Proof.Sm4.scheduleAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dK0
        · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base W (by decide))),
      g.out, hKey]
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄']; exact pC
  have pW' : Covers [⟨W, 768⟩] s₄.wr := by rw [wr₄']; exact pW
  -- `H = CIPH_K(0¹²⁸)`.
  have cc : CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) 1 := by
    refine ⟨x0₄, x1₄, x2₄, x3₄, by rw [sp₄']; exact hsp, by decide, ?_, by omega_arith, ?_,
      ?_, dK0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega_arith
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (W.toNat + 96 % 2 ^ 64) (2 ^ 64); omega_arith
    · simpa using dCW 0 128 (by decide) 96 16 (by decide)
    · exact (dCW 240 16 (by decide) 96 16 (by decide)).symm
    · rw [sp₄']; exact sC.sub_right (Region.sub_prefix (by decide))
    · rw [sp₄']; exact sW.sub_right (Offset.sub_base W (by decide))
    · rw [sp₄']; exact sC.sub_right (Offset.sub_base Ctx (by decide))
    · exact covers_cons (covers_left (covers_prefix pC' (by decide))) (covers_cons
        (covers_left (covers_off pW' (by decide) (by decide)))
        (covers_left (covers_off pC' (by decide) (by decide))))
    · exact covers_cons (covers_off pW' (by decide) (by decide)) (covers_off pC' (by decide) (by decide))
  refine WP.seq (WP.mono (ctr_call cc) fun s₅ c => ?_)
  have cf := c.frame
  rw [sp₄'] at cf
  have gout := c.out
  rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq, hT₄, hD₄, hk₄] at gout
  have c19 : s₅.gpr .x19 = W := by rw [c.saved .x19 (by decide) (by decide), og₄ _ (by decide), g19]
  have dSvK : ∀ r ∈ [(⟨Ctx, 128⟩ : Region), stk s.sp], (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base W (by decide)) |>.symm
    · exact (sW.sub_right (Offset.sub_base W (by decide))).symm
  have dSv₄ : ∀ r ∈ [(⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region), ⟨W + BitVec.ofNat 64 96, 16⟩],
      (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dCW 240 16 (by decide) 128 88 (by decide)).symm
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by omega_arith)
  have dSv₅ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region), ⟨Ctx + BitVec.ofNat 64 240, 16 * 1⟩, stk s.sp],
      (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by omega_arith)
    · exact (dCW 240 16 (by decide) 128 88 (by decide)).symm
    · exact (sW.sub_right (Offset.sub_base W (by decide))).symm
  have hsv₁ : SavedAt s₁.mem W s := by rw [m₁]; exact savedAt_save _ _ _
  have hsv₅ : SavedAt s₅.mem W s :=
    (((hsv₁.frame (by rw [← m₂]; exact gf) dSvK).frame f₄ dSv₄).frame cf dSv₅)
  have pWr : Covers [⟨W, 768⟩] (s₅.rd ++ s₅.wr) := by rw [c.rd, c.wr, rd₄', wr₄']; exact covers_left pW
  refine WP.mono (exit_ok c19 (by rw [c.sp, sp₄']) pWr hsv₅) fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_, ?_⟩
  · rw [hm, Proof.Sm4.scheduleAt_frame cf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base W (by decide))
      · exact dK0
      · exact (sC.sub_right (Region.sub_prefix (by decide))).symm), hk₄]
  · show blockAt s'.mem (Ctx + 240) = _
    rw [hm, ofNat_lit, gout.1]
    simp [Spec.Sm4.gcmCipherOfKey]

end VG.Proof.Sm4Gcm.AArch64
