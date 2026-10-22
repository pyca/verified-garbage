module

public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Init
import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Tag
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_init`

Untrusted: everything here is checked by Lean. The key schedule from
`vg_sm4_expand_key` in the context's first 128 bytes, then the hash subkey
`CIPH_K(0¹²⁸)` at byte 240 from `vg_sm4_ctr32` over a zero block with a zero
counter block (`init_wp`), as AES-GCM's (`Proof/AesGcm/X86_64/Init.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr save restore tO)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Proof.AesGcm.X86_64 (save_ok exit_ok SavedAt savedR ret_kept covers_left covers_cons covers_of_mem
  covers_off in_off covers_prefix add_ofNat_assoc zeroT_bytes bytesAt_frame blockAt_frame blocksAt_one
  ctr32_single ctxH_eq)

/-- The key, as SM4's block of 16 bytes. -/
theorem blockAt_eq_ofFn (m : Mem) (p : Addr) :
    Spec.Sm4.blockAt m p = Vector.ofFn fun i => (bytesAt m p 16).getD i.val 0 := by
  apply Vector.ext
  intro i hi
  simp [Spec.Sm4.blockAt, bytesAt, hi]

/-- `vg_sm4_gcm_init`. -/
theorem init_wp {s : State} (hp : Proof.Sm4Gcm.initX86_64.pre s) :
    WP isa init s fun s' => gprPreserved s s' ∧ Proof.Sm4Gcm.initX86_64.post s s' := by
  simp only [Proof.Sm4Gcm.initX86_64, Proof.Sm4Gcm.ret, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk] at hp ⊢
  obtain ⟨hrd, hwr, d_kc, d_ks, d_cs, r_c, r_s, k_k, k_c, k_s, wk, wc, ws, hsp⟩ := hp
  generalize hK : s.gpr .rdi = K at *
  generalize hCtx : s.gpr .rsi = Ctx at *
  generalize hW : s.gpr .rdx = W at *
  generalize hSP : s.gpr .rsp = SP at *
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s .rdx hW pW
  obtain ⟨s₂, run₂, h15, h13, hdi, hsi, hsp₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rdx), .mov .r13 (.reg .rsi)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .rdi = K ∧ s₂.gpr .rsi = Ctx ∧ s₂.gpr .rsp = SP ∧
      s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, hg₁, hW, hCtx, hK, hSP]
  refine WP.seq ?_
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  have rd₂ : s₂.rd = s.rd := hrd₂.trans hrd₁
  have wr₂ : s₂.wr = s.wr := hwr₂.trans hwr₁
  have kc : KeyCall s₂ K Ctx := by
    refine ⟨hdi, hsi, by rw [hsp₂]; exact hsp, wk, by omega, d_kc.sub_right (Region.sub_prefix (by decide)),
      by rw [hsp₂]; exact k_k, by rw [hsp₂]; exact k_c.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
    · rw [rd₂, wr₂, hrd]
      exact covers_cons (covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _)))
        (covers_left (covers_prefix pC (by decide)))
    · rw [wr₂]; exact covers_prefix pC (by decide)
  refine WP.seq (WP.mono (key_call kc) fun s₃ g => ?_)
  have g15 : s₃.gpr .r15 = W := by rw [g.saved .r15 (by decide), h15]
  have g13 : s₃.gpr .r13 = Ctx := by rw [g.saved .r13 (by decide), h13]
  have gsp : s₃.gpr .rsp = SP := by rw [g.saved .rsp (by decide), hsp₂]
  have rd₃ : s₃.rd = s.rd := g.rd.trans rd₂
  have wr₃ : s₃.wr = s.wr := g.wr.trans wr₂
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := in_off pW (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off pW (show 104 + 8 ≤ 2560 by decide) (by decide)
  rw [← wr₃] at w₁ w₂ w₃ w₄
  obtain ⟨s₄, run₄, hm₄, hdi₄, hsi₄, hdx₄, hcx₄, hg₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r13 240) .rax, .store (at_ .r13 248) .rax,
        .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax, .mov .rdi (.reg .r13)] ++
        ptr .rsi .r15 tO ++ ptr .rdx .r13 240 ++ [.mov32 .rcx (imm 1)]) s₃ = some s₄ ∧
      s₄.mem = (((s₃.mem.writeW (Ctx + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₄.gpr .rdi = Ctx ∧ s₄.gpr .rsi = W + BitVec.ofNat 64 96 ∧ s₄.gpr .rdx = Ctx + BitVec.ofNat 64 240 ∧
      s₄.gpr .rcx = BitVec.ofNat 64 1 ∧ (∀ r ∈ calleeSaved, s₄.gpr r = s₃.gpr r) ∧
      s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    rw [add_ofNat_assoc, add_ofNat_assoc]
    refine ⟨_, by xrun [g15, g13, w₁, w₂, w₃, w₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [mem_setReg, mem_arithFlags]
    · simp [gpr_setReg, gpr_arithFlags, g13]
    · simp [gpr_setReg, gpr_arithFlags, g15]
    · simp [gpr_setReg, gpr_arithFlags, g13]
    · simp [gpr_setReg, gpr_arithFlags]
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have g4sp : s₄.gpr .rsp = SP := by rw [hg₄ .rsp (by decide), gsp]
  have rd₄ : s₄.rd = s.rd := hrd₄.trans rd₃
  have wr₄ : s₄.wr = s.wr := hwr₄.trans wr₃
  -- The disjointness of the parts.
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 2560 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ he)
  have dK0 : (⟨Ctx, 128⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega)
  have f₄ : Frame [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact ((Cmac.frame_store2 _ _ _).mono (by simp)).trans ((Cmac.frame_store2 _ _ _).mono (by simp))
  have hT₄ : blockAt s₄.mem (W + BitVec.ofNat 64 96) = 0 := by
    rw [blockAt, hm₄, zeroT_bytes]; decide
  have hD₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = 0 := by
    rw [blockAt, hm₄, bytesAt_frame (Cmac.frame_store2 _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dCW 240 16 (by decide) 96 16 (by decide)) (by decide),
      zeroT_bytes]
    decide
  have hk₄ : Spec.Sm4.scheduleAt s₄.mem Ctx = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem K) := by
    rw [Proof.Sm4.scheduleAt_congr fun i hi => f₄.bytes (R := ⟨Ctx, 128⟩) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dK0
        · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide)))
        (by show 128 ≤ 2 ^ 64; omega) hi, g.out, hm₂]
    congr 1
    apply Vector.ext
    intro i hi
    simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
    exact f₁.bytes (R := ⟨K, 16⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d_ks.sub_right (Offset.sub_base _ (by decide)))
      (by show 16 ≤ 2 ^ 64; omega) hi
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄]; exact pC
  have pW' : Covers [⟨W, 2560⟩] s₄.wr := by rw [wr₄]; exact pW
  have cc : CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) 1 := by
    refine ⟨hdi₄, hsi₄, hdx₄, hcx₄, by rw [g4sp]; exact hsp, by omega,
      by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
      by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega,
      by simpa using dCW 0 128 (by decide) 96 16 (by decide), dK0,
      (dCW 240 16 (by decide) 96 16 (by decide)).symm, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g4sp]; exact k_c.sub_right (Region.sub_prefix (by decide))
    · rw [g4sp]; exact k_s.sub_right (Offset.sub_base _ (by decide))
    · rw [g4sp]; exact k_c.sub_right (Offset.sub_base _ (by decide))
    · exact covers_cons (covers_left (covers_prefix pC' (by decide))) (covers_cons
        (covers_left (covers_off pW' (by decide) (by decide)))
        (covers_left (covers_off pC' (by decide) (by decide))))
    · exact covers_cons (covers_off pW' (by decide) (by decide)) (covers_off pC' (by decide) (by decide))
  refine WP.seq (WP.mono (ctr_call cc) fun s₅ c => ?_)
  have gout := c.out
  rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq, hT₄, hD₄, hk₄] at gout
  have c15 : s₅.gpr .r15 = W := by rw [c.saved .r15 (by decide), hg₄ .r15 (by decide), g15]
  have c5sp : s₅.gpr .rsp = SP := by rw [c.saved .rsp (by decide), g4sp]
  have cfr := c.frame
  rw [g4sp] at cfr
  have gfr := g.frame
  rw [hsp₂] at gfr
  -- The saved registers and the return address.
  have dSv : ∀ r ∈ [(⟨Ctx, 128⟩ : Region), below SP stkN], (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide)) |>.symm
    · exact (k_s.sub_right (Offset.sub_base _ (by decide))).symm
  have dSv₄ : ∀ r ∈ [(⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region), ⟨W + BitVec.ofNat 64 96, 16⟩], (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dCW 240 16 (by decide) 128 48 (by decide)).symm
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  have dSv₅ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region), ⟨Ctx + BitVec.ofNat 64 240, 16 * 1⟩, below SP stkN],
      (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
    · exact (dCW 240 16 (by decide) 128 48 (by decide)).symm
    · exact (k_s.sub_right (Offset.sub_base _ (by decide))).symm
  have hsv₅ : SavedAt s₅.mem W s :=
    (((hsv₁.frame (by rw [← hm₂]; exact gfr) dSv).frame f₄ dSv₄).frame cfr dSv₅)
  have hret : s₅.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept cfr (fun r hr => ?_), ret_kept f₄ (fun r hr => ?_), ret_kept gfr (fun r hr => ?_), hm₂,
      ret_kept f₁ (fun r hr => ?_)]
    · simp only [List.mem_singleton] at hr; subst hr; exact r_s.sub_right (Offset.sub_base _ (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact r_c.sub_right (Region.sub_prefix (by decide))
      · exact ret_stk SP
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact r_c.sub_right (Offset.sub_base _ (by decide))
      · exact r_s.sub_right (Offset.sub_base _ (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact r_s.sub_right (Offset.sub_base _ (by decide))
      · exact r_c.sub_right (Offset.sub_base _ (by decide))
      · exact ret_stk SP
  have hrc : Covers [⟨W, 2560⟩] (s₅.rd ++ s₅.wr) := by rw [c.rd, c.wr, rd₄, wr₄]; exact covers_left pW
  refine WP.mono (exit_ok c15 (by rw [c5sp, hSP]) hrc hsv₅ (by rw [hSP]; exact hret)) fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_⟩
  rw [hm]
  refine ⟨?_, ?_⟩
  · rw [Proof.Sm4.scheduleAt_congr fun i hi => cfr.bytes (R := ⟨Ctx, 128⟩) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
        · exact dK0
        · exact (k_c.sub_right (Region.sub_prefix (by decide))).symm)
        (by show 128 ≤ 2 ^ 64; omega) hi, hk₄, blockAt_eq_ofFn]
  · rw [ctxH_eq, gout.1, Spec.Sm4.gcmCipherOfKey, blockAt_eq_ofFn]
    simp

end VG.Proof.Sm4Gcm.X86_64
