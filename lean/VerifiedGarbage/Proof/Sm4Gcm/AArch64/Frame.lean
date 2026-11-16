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
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.InitCT
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.StreamCryptCT
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.FinCT
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.SealCT
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.OpenCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.StreamCrypt
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Seal
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Open
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.StreamFinish
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Sm4Gcm.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-! ### `Sm4Gcm.AArch64.Verified`, which only this module used -/

section

/-! ### `Sm4Gcm.AArch64.Init`, which only this module used -/

section

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
theorem init_wp (v : GcmImpl) {s : State} (hp : initAArch64.pre s) :
    WP isa (init v.callees) s fun s' => GprAbi s s' ∧ initAArch64.post s s' := by
  simp only [initAArch64] at hp ⊢
  obtain ⟨hsp, hrd, hwr, d_kc, d_ks, d_cs, sK, sC, sW, fK, fC, fW⟩ := hp
  generalize hK : s.gpr .x0 = K at *
  generalize hCtx : s.gpr .x1 = Ctx at *
  generalize hW : s.gpr .x2 = W at *
  obtain pW : Covers [⟨W, 768⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  obtain pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  obtain pK : Covers [⟨K, 16⟩] (s.rd ++ s.wr) := by rw [hrd]; exact covers_of_mem (by simp)
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
  obtain rd₂' : s₂.rd = s.rd := rd₂.trans rd₁
  obtain wr₂' : s₂.wr = s.wr := wr₂.trans wr₁
  obtain sp₂' : s₂.sp = s.sp := sp₂.trans sp₁
  -- The key schedule.
  obtain kc : KeyCall s₂ K Ctx := by
    refine ⟨x0₂, x1₂, by rw [sp₂']; exact hsp, fK, by omega_arith, d_kc.sub_right (Region.sub_prefix (by decide)),
      by rw [sp₂']; exact sK, by rw [sp₂']; exact sC.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
    · rw [rd₂', wr₂']
      exact covers_cons pK (covers_left (covers_prefix pC (by decide)))
    · rw [wr₂']; exact covers_prefix pC (by decide)
  refine WP.seq (WP.mono (key_call v.ctr.key kc) fun s₃ g => ?_)
  obtain g19 : s₃.gpr .x19 = W := by rw [g.saved .x19 (by decide) (by decide), x19₂]
  obtain g21 : s₃.gpr .x21 = Ctx := by rw [g.saved .x21 (by decide) (by decide), x21₂]
  obtain rd₃ : s₃.rd = s.rd := g.rd.trans rd₂'
  obtain wr₃ : s₃.wr = s.wr := g.wr.trans wr₂'
  obtain sp₃ : s₃.sp = s.sp := g.sp.trans sp₂'
  have gf := g.frame
  rw [sp₂'] at gf
  -- A zero block at the context's `H` and a zero counter block in `T`.
  obtain w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  obtain w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  obtain w₃ := in_off pW (show 96 + 8 ≤ 768 by decide) (by decide)
  obtain w₄ := in_off pW (show 104 + 8 ≤ 768 by decide) (by decide)
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
  obtain rd₄' : s₄.rd = s.rd := rd₄.trans rd₃
  obtain wr₄' : s₄.wr = s.wr := wr₄.trans wr₃
  obtain sp₄' : s₄.sp = s.sp := sp₄.trans sp₃
  obtain dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 768 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ he)
  obtain dK0 : (⟨Ctx, 128⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega_arith)
  obtain e248 : Ctx + BitVec.ofNat 64 248 = Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 :=
    (add_ofNat_assoc _ 240 8).symm
  obtain e104 : W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 :=
    (add_ofNat_assoc _ 96 8).symm
  rw [e248, e104] at hm₄
  obtain f₄ : Frame [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact ((Proof.Cmac.frame_store2 _ _ _).mono (by simp)).trans ((Proof.Cmac.frame_store2 _ _ _).mono (by simp))
  obtain hT₄ : blockAt s₄.mem (W + BitVec.ofNat 64 96) = 0 := by
    rw [blockAt, hm₄, zeroT_bytes]; decide
  obtain hD₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = 0 := by
    rw [blockAt, hm₄, bytesAt_frame (Proof.Cmac.frame_store2 _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dCW 240 16 (by decide) 96 16 (by decide)) (by decide),
      zeroT_bytes]
    decide
  obtain fsv : Frame [savedR W] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  -- The key, as the callee read it, and the schedule.
  obtain hKey : Spec.Sm4.blockAt s₂.mem K = Vector.ofFn fun i : Fin 16 => (bytesAt s.mem K 16).getD i.val 0 := by
    rw [sm4BlockAt_eq, m₂, bytesAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d_ks.sub_right (Offset.sub_base W (by decide)))
      (by decide)]
  obtain hk₄ : Spec.Sm4.scheduleAt s₄.mem Ctx =
      Spec.Sm4.expandKey (Vector.ofFn fun i : Fin 16 => (bytesAt s.mem K 16).getD i.val 0) := by
    rw [Proof.Sm4.scheduleAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dK0
        · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base W (by decide))),
      g.out, hKey]
  obtain pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄']; exact pC
  obtain pW' : Covers [⟨W, 768⟩] s₄.wr := by rw [wr₄']; exact pW
  -- `H = CIPH_K(0¹²⁸)`.
  obtain cc : CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) 1 := by
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
  refine WP.seq (WP.mono (ctr_call v.ctr cc) fun s₅ c => ?_)
  have cf := c.frame
  rw [sp₄'] at cf
  have gout := c.out
  rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq, hT₄, hD₄, hk₄] at gout
  obtain c19 : s₅.gpr .x19 = W := by rw [c.saved .x19 (by decide) (by decide), og₄ _ (by decide), g19]
  obtain dSvK : ∀ r ∈ [(⟨Ctx, 128⟩ : Region), stk s.sp], (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base W (by decide)) |>.symm
    · exact (sW.sub_right (Offset.sub_base W (by decide))).symm
  obtain dSv₄ : ∀ r ∈ [(⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region), ⟨W + BitVec.ofNat 64 96, 16⟩],
      (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dCW 240 16 (by decide) 128 88 (by decide)).symm
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by omega_arith)
  obtain dSv₅ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region), ⟨Ctx + BitVec.ofNat 64 240, 16 * 1⟩, stk s.sp],
      (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by omega_arith)
    · exact (dCW 240 16 (by decide) 128 88 (by decide)).symm
    · exact (sW.sub_right (Offset.sub_base W (by decide))).symm
  obtain hsv₁ : SavedAt s₁.mem W s := by rw [m₁]; exact savedAt_save _ _ _
  obtain hsv₅ : SavedAt s₅.mem W s :=
    (((hsv₁.frame (by rw [← m₂]; exact gf) dSvK).frame f₄ dSv₄).frame cf dSv₅)
  obtain pWr : Covers [⟨W, 768⟩] (s₅.rd ++ s₅.wr) := by rw [c.rd, c.wr, rd₄', wr₄']; exact covers_left pW
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

end

end


/-!
# SM4-GCM on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_ghash` and `vg_sm4_ctr32`), a state satisfying each
precondition, and the shared contracts of `Spec/Sm4/Gcm/Contract.lean` with
the working space as a last argument (`Sig.scratchContract`) and the 3264
bytes of stack `vg_sm4_ctr32` and `vg_sm4_expand_key` use below the stack
pointer.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (minK copy copyB xorB tagLenOk tagIn cmpSeg cmp cmp16 fo textArgs tagOut restore)

/-- The CPU features of the functions calling `vg_ghash`: its implementation's. -/
def GcmImpl.features (v : GcmImpl) : List String := v.gh.features

/-! ## v8–v15 -/

theorem init_keepsV (v : GcmImpl) : (init v.callees).allInstrs keepsV = true := by
  simp only [init, ctrCall, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.ctr.key.keepsV]; lit_decide

theorem streamEncrypt_keepsV (v : GcmImpl) : (streamEncrypt v.callees).allInstrs keepsV = true := by
  simp only [streamEncrypt, encBody, fo, textAbs, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall, absorb,
    absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees,
    Code.allInstrs, v.ctr.keepsV, v.gh.keepsV]; lit_decide

theorem streamDecrypt_keepsV (v : GcmImpl) : (streamDecrypt v.callees).allInstrs keepsV = true := by
  simp only [streamDecrypt, decBody, decAbs, fo, textAbs, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall,
    absorb, absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens,
    GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.gh.keepsV]; lit_decide

theorem streamFinish_keepsV (v : GcmImpl) : (streamFinish v.callees).allInstrs keepsV = true := by
  simp only [streamFinish, finBody, tag, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, xorB,
    Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV,
    v.gh.keepsV]; lit_decide

theorem streamVerify_keepsV (v : GcmImpl) : (streamVerify v.callees).allInstrs keepsV = true := by
  simp only [streamVerify, tagLenOk, tagIn, cmpSeg, cmp, cmp16, finBody, tag, ctrCall, ghCall, absorb,
    absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees,
    Code.allInstrs, v.ctr.keepsV, v.gh.keepsV]; lit_decide

theorem seal_keepsV (v : GcmImpl) : («seal» v.callees).allInstrs keepsV = true := by
  simp only [«seal», sealRest, j0, j0hash, oneAad, absorbAl, encBody, fo, textAbs, finBody, tag, crypt, crSeg1,
    crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor,
    padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.gh.keepsV]; lit_decide

theorem open_keepsV (v : GcmImpl) : («open» v.callees).allInstrs keepsV = true := by
  simp only [«open», openEntry, openRest, openMain, oneCrypt, cryptAl, crArgs, tagLenOk, tagIn, cmpSeg, cmp,
    cmp16, j0, j0hash, oneAad, absorbAl, decAbs, fo, textAbs, finBody, tag, crypt, crSeg1, crSeg2, crTail,
    ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush,
    lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.gh.keepsV]
  lit_decide

/-! ## Correctness -/

theorem init_correct (v : GcmImpl) (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa (init v.callees) s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (init_wp v hs) (init_keepsV v)

theorem streamEncrypt_correct (v : GcmImpl) (s : State) (hs : streamEncryptAArch64.pre s) :
    ∃ t s', Exec isa (streamEncrypt v.callees) s t s' ∧ abiPreserved s s' ∧ streamEncryptAArch64.post s s' :=
  WP.withPreservedV (streamEncrypt_wp v hs) (streamEncrypt_keepsV v)

theorem streamDecrypt_correct (v : GcmImpl) (s : State) (hs : streamDecryptAArch64.pre s) :
    ∃ t s', Exec isa (streamDecrypt v.callees) s t s' ∧ abiPreserved s s' ∧ streamDecryptAArch64.post s s' :=
  WP.withPreservedV (streamDecrypt_wp v hs) (streamDecrypt_keepsV v)

theorem streamFinish_correct (v : GcmImpl) (s : State) (hs : streamFinishAArch64.pre s) :
    ∃ t s', Exec isa (streamFinish v.callees) s t s' ∧ abiPreserved s s' ∧ streamFinishAArch64.post s s' :=
  WP.withPreservedV (streamFinish_wp v hs) (streamFinish_keepsV v)

theorem streamVerify_correct (v : GcmImpl) (s : State) (hs : streamVerifyAArch64.pre s) :
    ∃ t s', Exec isa (streamVerify v.callees) s t s' ∧ abiPreserved s s' ∧ streamVerifyAArch64.post s s' :=
  WP.withPreservedV (streamVerify_wp v hs) (streamVerify_keepsV v)

theorem seal_correct (v : GcmImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (seal_wp v hs) (seal_keepsV v)

theorem open_correct (v : GcmImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (open_wp v hs) (open_keepsV v)

/-! ## States satisfying the preconditions (with empty buffers)

The stack pointer is `0x8000`, and the 3264 bytes below it are apart from
every buffer. -/

def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 768⟩]

def streamCryptSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x4 => 0x2000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 768⟩]

def finSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x4 => 0x5000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 768⟩]

def verSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x4 => 0x5000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 768⟩]

/-- `tag` at `0x6000` and `work` at `0x5000` (`[sp]`). -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | .x7 => 0x6000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8001 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x6000, 16⟩, ⟨0x5000, 768⟩]

/-- `tag` at `0x6000`, `tag_len` 0 (`[sp]`) and `work` at `0x5000` (`[sp + 8]`). -/
def openSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | .x7 => 0x6000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8009 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x6000, 0⟩, ⟨0x8000, 16⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 768⟩]

/-! ## The shared contracts -/

theorem init_verified (v : GcmImpl) :
    Verified AArch64.target (init v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.initSig "scratch" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.initPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.initSig,
      Spec.Sm4.Gcm.initPost, initAArch64, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow]
      [initSat] using initSat)

theorem streamEncrypt_verified (v : GcmImpl) :
    Verified AArch64.target (streamEncrypt v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.streamCryptSig "scratch" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamEncryptPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (streamEncrypt_correct v) (streamEncrypt_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamEncryptPost, streamEncryptAArch64, streamCryptPre, streamCryptPub]
      [streamCryptSat] using streamCryptSat)

theorem streamDecrypt_verified (v : GcmImpl) :
    Verified AArch64.target (streamDecrypt v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.streamCryptSig "scratch" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamDecryptPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (streamDecrypt_correct v) (streamDecrypt_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamDecryptPost, streamDecryptAArch64, streamCryptPre, streamCryptPub]
      [streamCryptSat] using streamCryptSat)

theorem streamFinish_verified (v : GcmImpl) :
    Verified AArch64.target (streamFinish v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.streamFinishSig "work" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamFinishPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (streamFinish_correct v) (streamFinish_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost, streamFinishAArch64, finPre]
      [finSat] using finSat)

theorem streamVerify_verified (v : GcmImpl) :
    Verified AArch64.target (streamVerify v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.streamVerifySig "work" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamVerifyPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (streamVerify_correct v) (streamVerify_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost, streamVerifyAArch64, verPre]
      [verSat] using verSat)

theorem seal_verified (v : GcmImpl) :
    Verified AArch64.target («seal» v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.sealSig "work" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.sealPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost, sealAArch64, sealPre, onePub]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified (v : GcmImpl) :
    Verified AArch64.target («open» v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.openSig "work" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.openPost AArch64.abi.ptrBits) true 3264 (some (Spec.Sm4.Gcm.openLeak AArch64.abi.ptrBits))) :=
  Verified.of_correct (open_correct v) (open_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost, openAArch64, openPre, onePub, openRes, openLeakOf, Spec.Sm4.Gcm.openLeak, stackArg, stackArgAddr, Curry.app, Option.map]
      [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat)

end VG.Proof.Sm4Gcm.AArch64

end

end


/-!
# SM4-GCM on AArch64, with its working space on the stack

Every function of SM4-GCM runs its code, proved with the working space as its
last argument (`Verified.lean`), in a frame that allocates it: 768 bytes for
the working space in a register (`Verified.stackScratch`); for `seal` and
`open`, whose working space is their first and second stack argument, 784
bytes that also hold a copy of the stack argument before it, if any
(`Verified.stackArgScratch`). Below the frame, the code's calls of
`vg_sm4_ctr32` and `vg_sm4_expand_key` use 3264 bytes of stack.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.Impl.Sm4Gcm.AArch64

/-- A state satisfying `vg_sm4_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.initContract AArch64.abi 4032).pre s := by
  implies_sat [Spec.Sm4.Gcm.initContract, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost, AArch64.abi,
    AArch64.argRegs, stackBelow] [initFrameSat, initSat] using initFrameSat

theorem init_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 768 .x2 (init v.callees))
      (Spec.Sm4.Gcm.initContract AArch64.abi 4032) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.initPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 768)
    (init_verified v) (by decide) (by decide) initFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_encrypt`'s precondition, without the working
space. -/
def streamEncryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamEncryptContract AArch64.abi 4032).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamEncryptContract, Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamEncryptPost, AArch64.abi,
    AArch64.argRegs, stackBelow] [streamEncryptFrameSat, streamCryptSat] using streamEncryptFrameSat

theorem streamEncrypt_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (streamEncrypt v.callees))
      (Spec.Sm4.Gcm.streamEncryptContract AArch64.abi 4032) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.streamEncryptPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 768)
    (streamEncrypt_verified v) (by decide) (by decide) streamEncryptFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_decrypt`'s precondition, without the working
space. -/
def streamDecryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamDecryptContract AArch64.abi 4032).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamDecryptContract, Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamDecryptPost, AArch64.abi,
    AArch64.argRegs, stackBelow] [streamDecryptFrameSat, streamCryptSat] using streamDecryptFrameSat

theorem streamDecrypt_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (streamDecrypt v.callees))
      (Spec.Sm4.Gcm.streamDecryptContract AArch64.abi 4032) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.streamDecryptPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 768)
    (streamDecrypt_verified v) (by decide) (by decide) streamDecryptFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition, without the working
space. -/
def streamFinishFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem streamFinishFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamFinishContract AArch64.abi 4032).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamFinishContract, Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost, AArch64.abi,
    AArch64.argRegs, stackBelow] [streamFinishFrameSat, finSat] using streamFinishFrameSat

theorem streamFinish_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 768 .x5 (streamFinish v.callees))
      (Spec.Sm4.Gcm.streamFinishContract AArch64.abi 4032) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamFinishSig) (nm := "work") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.streamFinishPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 768)
    (streamFinish_verified v) (by decide) (by decide) streamFinishFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition, without the working
space. -/
def streamVerifyFrameSat : State := { verSat with wr := [⟨0x3000, 80⟩] }

theorem streamVerifyFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamVerifyContract AArch64.abi 4032).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamVerifyContract, Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost, AArch64.abi,
    AArch64.argRegs, stackBelow] [streamVerifyFrameSat, verSat] using streamVerifyFrameSat

theorem streamVerify_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (streamVerify v.callees))
      (Spec.Sm4.Gcm.streamVerifyContract AArch64.abi 4032) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamVerifySig) (nm := "work") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.streamVerifyPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 768)
    (streamVerify_verified v) (by decide) (by decide) streamVerifyFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition, without the working
space: no stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩], wr := [⟨0x4000, 0⟩, ⟨0x6000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.sealContract AArch64.abi 4048).pre s := by
  implies_sat [Spec.Sm4.Gcm.sealContract, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop, stackBelow] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 784 0 («seal» v.callees))
      (Spec.Sm4.Gcm.sealContract AArch64.abi 4048) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 3264)
    (bytes := 784) (seal_verified v) (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _)
    (Proof.Sm4Gcm.sealPost_local (pb := AArch64.abi.ptrBits)) sealFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_open`'s precondition, without the working
space: `tag_len` 0, its one stack argument. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x6000, 0⟩, ⟨0x8000, 8⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.openContract AArch64.abi 4048).pre s := by
  implies_sat [Spec.Sm4.Gcm.openContract, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost,
    Spec.Sm4.Gcm.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
    List.getD, List.range, List.range.loop, stackBelow] [openFrameSat, openSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 784 1 («open» v.callees))
      (Spec.Sm4.Gcm.openContract AArch64.abi 4048) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.openPost AArch64.abi.ptrBits) (wa := true) (stack := 3264)
    (bytes := 784) (leak := some (Spec.Sm4.Gcm.openLeak AArch64.abi.ptrBits))
    (open_verified v) (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _)
    (Proof.Sm4Gcm.openPost_local (pb := AArch64.abi.ptrBits)) openFrameSat_pre
    (hleak := Proof.Sm4Gcm.openLeak_local (pb := AArch64.abi.ptrBits))

end VG.Proof.Sm4Gcm.AArch64
