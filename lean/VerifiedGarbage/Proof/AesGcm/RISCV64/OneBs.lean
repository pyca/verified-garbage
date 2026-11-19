module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
public import VerifiedGarbage.Impl.AesGcm.RISCV64
import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.J0
import VerifiedGarbage.Proof.AesGcm.RISCV64.Tag
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM on RISC-V: the one-shot functions with the round keys bitsliced

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_bitsliced`
is `vg_aes_gcm_seal` with `bk` as its second stack argument, loaded into `s7`
once `J₀` (which reads the nonce's length there) is done (`bkLoad`), and
`vg_aes_ctr32_bs` on it for `vg_aes_ctr32` (`oneCryptB`, `oneTagB`). The
buffer's round keys reach those calls through the frames of what runs
before them (`BkIn`, from `CtxSlicedRepr` by `keysAt_of_sliced`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ghashInput fullTag zeros padLen j0 inc32 gctr encryptWith toBytes)
open VG.Proof.Gcm (Absorbed)

/-- `bkLoad off`: `s7 := [sp + off]`. -/
theorem bkLoad_ok {s : State} {off : Nat} (ho : off < 2048) (hsa : s.sp.toNat % 16 = 0) (hd : off % 8 = 0)
    (hi : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 off) 8) :
    WP isa (.block (bkLoad off)) s fun s' => s'.gpr .s7 = s.mem.readW (s.sp + BitVec.ofNat 64 off) 64 ∧
      (∀ r, r ≠ .t2 → r ≠ .s7 → s'.gpr r = s.gpr r) ∧ Keeps s s' :=
  Steps.wp_addSp (imm := 0) (by decide) fun sA uA =>
    Steps.wp_ld (off := off) (a := s.sp + BitVec.ofNat 64 off) ho (by rw [uA.gpr, add_ofNat_zero])
      (Spill.al8 (B := s.sp) (by omega_using [hsa]) hd) (by rw [uA.rd, uA.wr]; exact hi) fun sB uB =>
      WP.block_nil ⟨by rw [uB.gpr, uA.mem], fun r h2 h7 => by rw [uB.other r h7, uA.other r h2],
        ⟨by rw [uB.mem, uA.mem], by rw [uB.rd, uA.rd], by rw [uB.wr, uA.wr], by rw [uB.sp, uA.sp]⟩⟩

theorem sealBs_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : sealBsRISCV64.pre s₀) :
    WP isa sealBs s₀ fun s' => abiPreserved s₀ s' ∧ sealBsRISCV64.post s₀ s' := by
  have h' : sealBsPre s₀ := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, dbd, dbW, fc, fn, fa, fd, fW, fsp, hR,
    hstk, ca, wa, ba, hsl⟩ := h'
  obtain L₀ := oneLay fc fW dcW ca wa
  obtain hk₀ : StkOk (s₀.gpr .a0) (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₀.sp :=
    one_stk hstk (by simp) (by simp)
  obtain hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain hW : Covers [⟨stackArg s₀ 2, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hA : Covers [args s₀ 3] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain hTd : (⟨s₀.sp + BitVec.ofNat 64 0, 8⟩ : Region).Disjoint (oneR (stackArg s₀ 2)) :=
    ((dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).sub_right
      (Region.sub_prefix (show 8 ≤ 8 * 3 by decide))).symm
  refine WP.seq (WP.mono (one1_wp (off := 16) (W := stackArg s₀ 2) (T := stackArg s₀ 0) (.inr rfl) hW wa hstk.1
    (args_in hA (by decide) (i := 2) (by decide)) rfl (args_in hA (by decide) (i := 0) (by decide)) rfl hTd)
    fun s₁ h1 => ?_)
  obtain he₁ := one_env h1 hC hW hk₀
  obtain L := L₀.v h1.s2 h1.s1 h1.s0
  have f₁ := h1.frame
  have hk₁ := h1.keeps
  obtain cO : ∀ r ∈ [oneR (stackArg s₀ 2)], (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dcW.sub_right (Lay.wSub (by decide))
  -- `oneAad`
  obtain hH₁ : blockAt s₁.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
    rw [h1.s2]; exact ctxH_keep f₁ cO
  obtain hN : DataOk (s₁.gpr .s1) (s₁.gpr .s0) s₁ (s₀.gpr .a2) (s₀.gpr .a3).toNat := by
    rw [h1.s1, h1.s0]
    exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)), (s₀.gpr .a3).isLt,
      fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  obtain hAd : DataOk (s₁.gpr .s1) (s₁.gpr .s0) s₁ (s₀.gpr .a4) (s₁.gpr .s10).toNat := by
    rw [h1.s1, h1.s0, h1.s10]
    exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)), (s₀.gpr .a5).isLt,
      fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  obtain toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₁ hH₁ h1.s4 (by rw [h1.s5]; exact toN)
    (by rw [h1.s7]; exact toN) hN hAd (by rw [h1.s0]; exact h1.aad))) fun s₂ ⟨oa, rd₂, wr₂, sp₂⟩ => ?_)
  -- `bkLoad 8`: `s7 := bk`, the stack argument, which nothing has written
  obtain fA : Frame (oneR (stackArg s₀ 2) :: j0Frame (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₀.sp)
      s₀.mem s₂.mem := by
    have jf := oa.frame
    rw [h1.s1, h1.s0] at jf
    exact (f₁.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..).trans
      (jf.mono fun r hr => List.mem_cons_of_mem _ hr)
  obtain dAr : ∀ r ∈ oneR (stackArg s₀ 2) :: j0Frame (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₀.sp,
      (args s₀ 3).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact dWA.symm.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact dWA.symm.sub_right (Lay.wSub (by decide))
      · exact dWA.symm.sub_right (Lay.wSub (by decide))
      · exact dWA.symm.sub_right (Lay.wSub (by decide))
      · exact (stkAll_mem hstk.2.2 (by simp)).symm
  obtain hbk : s₂.mem.readW (s₂.sp + BitVec.ofNat 64 8) 64 = stackArg s₀ 1 := by
    rw [sp₂, hk₁.sp, slot_keep fA fun r hr => (dAr r hr).sub_left (Offset.sub s₀.sp (d := 8) (n := 8) (e := 0)
      (k := 24) (by decide) (by decide))]
    rfl
  refine WP.seq (WP.mono (bkLoad_ok (s := s₂) (off := 8) (by decide) (by rw [sp₂, hk₁.sp]; exact hstk.1) (by decide)
    (by rw [rd₂, wr₂, hk₁.rd, hk₁.wr, sp₂, hk₁.sp]; exact args_in hA (by decide) (i := 1) (by decide)))
    fun s₂' ⟨b7, g₂', k₂'⟩ => ?_)
  rw [hbk] at b7
  obtain he₂' := oa.env.set7 b7 (fun r hr h7 => g₂' r (by rintro rfl; exact absurd hr (by decide)) h7) k₂'.sp
    k₂'.rd k₂'.wr
  obtain dcA : ∀ r ∈ oneR (stackArg s₀ 2) :: j0Frame (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₀.sp,
      (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact dcW.sub_right (Lay.wSub (by decide))
    · exact ctx_j0Frame L₀ hk₀ r hr
  obtain dbA : ∀ r ∈ oneR (stackArg s₀ 2) :: j0Frame (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₀.sp,
      (⟨stackArg s₀ 1, 960⟩ : Region).Disjoint r := by
    obtain db : (⟨stackArg s₀ 1, 960⟩ : Region).Disjoint ⟨stackArg s₀ 2, 2560⟩ :=
      dbW.sub_left (Region.sub_prefix (by decide))
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact db.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact db.sub_right (Lay.wSub (by decide))
      · exact db.sub_right (Lay.wSub (by decide))
      · exact db.sub_right (Lay.wSub (by decide))
      · exact (stkAll_mem hstk.2.2 (r := ⟨stackArg s₀ 1, 1248⟩) (by simp)).symm.sub_left (Region.sub_prefix (by decide))
  obtain hR14 : (s₀.gpr .a1).toNat ≤ 14 := by rcases hR with h | h | h <;> omega_using [h]
  -- `oneCrypt`
  obtain hd₂ : DataW (s₁.gpr .s2) (s₁.gpr .s1) (s₁.gpr .s0) s₂ (s₀.gpr .a6) (s₁.gpr .s11).toNat := by
    rw [h1.s2, h1.s1, h1.s0, h1.s11]
    obtain hDw : Covers [⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩] s₂.wr := by
      rw [wr₂, hk₁.wr, hwr]; exact covers_mem (by simp)
    exact ⟨⟨covers_left hDw, (s₀.gpr .a7).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW,
      by rw [sp₂, hk₁.sp]; exact hstk.buf (by simp)⟩, hDw, dcd⟩
  obtain h28 : s₁.gpr .s3 = BitVec.ofNat 64 (s₀.gpr .a1).toNat := by rw [h1.s3]; exact toN
  obtain hD₂s : s₂.mem.readW (s₁.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6 := by
    rw [slot_keep oa.frame (slot_j0 L he₁.stk' (by decide)), h1.s0]; exact h1.dat
  obtain hbk₂ : BkIn (stackArg s₀ 1) (s₁.gpr .s2) (s₁.gpr .s1) (s₁.gpr .s0) s₀.sp (s₀.gpr .a1).toNat s₂.mem
      (s₀.gpr .a6) (s₀.gpr .a6) (s₁.gpr .s11).toNat s₂' := by
    rw [h1.s2, h1.s1, h1.s0, h1.s11]
    refine ⟨?_, ba, ?_, dbW.sub_left (Region.sub_prefix (by decide)),
      (stkAll_mem hstk.2.2 (r := ⟨stackArg s₀ 1, 1248⟩) (by simp)).symm.sub_left (Region.sub_prefix (by decide)),
      dbd.sub_left (Region.sub_prefix (by decide)), dbd.sub_left (Region.sub_prefix (by decide)), ?_⟩
    · rw [k₂'.rd, k₂'.wr, rd₂, wr₂, hk₁.rd, hk₁.wr]
      exact covers_appL (covers_prefix (k := 1248) (covers_mem (by rw [hrd]; simp)) (by decide))
    · exact (dbW.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
    · exact keysAt_ctx_frame hR fA dbA dcA (keysAt_of_sliced hR14 hsl)
  obtain hd₂' := hd₂.of_eq k₂'.rd k₂'.wr k₂'.sp
  refine WP.seq (WP.mono (WP.with_rdwr (oneCryptB_ok (V := setS7 s₁.gpr (stackArg s₀ 1)) (bs := true) (o := false) (icb := inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₁.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat))) L he₂' h28 hR
    hd₂' hd₂'.ok rfl (fun h => Bool.noConfusion h) (by rw [k₂'.mem]; exact hD₂s) (by rw [k₂'.mem]; exact oa.cb)
    fun _ => by rw [k₂'.mem]; exact hbk₂)) fun s₃ ⟨oc, rd₃, wr₃, sp₃⟩ => ?_)
  rw [k₂'.mem] at oc
  -- `oneTag 0`
  obtain hH₃ : blockAt s₃.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
    rw [blockAt_frame oc.frame (fun r hr => (ctx_crFrame L hd₂ r hr).sub_left (Lay.ctxSub (by decide)))]
    exact oa.hH
  obtain hb := Nat.mod_lt (bytesAt s₁.mem (s₀.gpr .a4) (s₁.gpr .s10).toNat ++
    zeros (padLen (bytesAt s₁.mem (s₀.gpr .a4) (s₁.gpr .s10).toNat).length)).length (show 16 > 0 by decide)
  obtain hab₃ := oa.abs.congr (blockAt_frame oc.frame (stp_crFrame L hd₂ (by decide)))
    (bytesAt_frame oc.frame (stp_crFrame L hd₂ (by omega_using [])) (by omega_using []))
  obtain hD₃s : s₃.mem.readW (s₁.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6 := by
    rw [slot_keep oc.frame (slot_crFrame L hd₂ (by decide))]; exact hD₂s
  refine WP.seq (WP.mono (WP.with_rdwr (oneTagB_ok (V := setS7 s₁.gpr (stackArg s₀ 1)) (bs := true) L (o := 0)
    (.inl rfl) oc.env h28 hR hH₃ (length_bytesAt _ _ _).symm hab₃ (hd₂'.ok.of_eq rd₃ wr₃ sp₃) hD₃s
    fun _ => hbk₂.frame hR oc.frame hbk₂.crFrame (ctx_crFrame L hd₂) rd₃ wr₃)) fun s₄ ⟨ot, rd₄, wr₄, _⟩ => ?_)
  -- the tag copied out
  obtain hTw : Covers [⟨s₁.gpr .s9, 16⟩] s₄.wr := by
    rw [wr₄, wr₃, k₂'.wr, wr₂, hk₁.wr, h1.s9, hwr]; exact covers_mem (by simp)
  obtain hTd' : (⟨s₁.gpr .s9, 16⟩ : Region).Disjoint ⟨s₁.gpr .s0, 16⟩ := by
    rw [h1.s9, h1.s0]; exact dtW.sub_right (Region.sub_prefix (by decide))
  refine WP.seq (WP.mono (tagOut_ok ot.env hTw hTd') fun s₅ ⟨hb₅, hf₅, g₅, k₅⟩ => ?_)
  simp only [setS7, reduceCtorEq, ↓reduceIte] at hb₅ hf₅
  obtain he₅ := ot.env.keep (fun r hr => g₅ r (by revert r; decide)) k₅.sp k₅.rd k₅.wr
  have of₄ := ot.frame
  simp only [setS7, reduceCtorEq, ↓reduceIte] at of₄
  rw [h1.s1, h1.s0] at of₄
  have cf₃ := oc.frame
  simp only [setS7, reduceCtorEq, ↓reduceIte] at cf₃
  rw [h1.s1, h1.s0, h1.s11] at cf₃
  have jf₂ := oa.frame
  rw [h1.s1, h1.s0] at jf₂
  obtain hd₂₀ : DataW (s₀.gpr .a0) (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₂ (s₀.gpr .a6)
      (s₀.gpr .a7).toNat := by rw [← h1.s2, ← h1.s1, ← h1.s0, ← h1.s11]; exact hd₂
  have sv₁ : SavedAt s₁.mem (stackArg s₀ 2) s₀ := h1.saved
  obtain sv₅ : SavedAt s₅.mem (stackArg s₀ 2) s₀ :=
    (((sv₁.frame jf₂ (saved_j0Frame L₀ hk₀)).frame cf₃ (saved_crFrame L₀ hd₂₀)).frame of₄
      (saved_otFrame L₀ hk₀ (.inl rfl))).frame (by rw [h1.s9] at hf₅; exact hf₅) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dtW.sub_right (Lay.wSub (by decide))).symm)
  obtain e31 : s₅.gpr .s0 = stackArg s₀ 2 := (he₅.fr _ (by decide)).trans h1.s0
  refine WP.mono (restore_ok e31 wa (by have := he₅.perm.w; simp only [setS7, reduceCtorEq, ↓reduceIte] at this; rw [h1.s0] at this; exact Covers.right this) sv₅
    he₅.sp) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  -- the results
  obtain f₂ : Frame (oneR (stackArg s₀ 2) :: j0Frame (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₀.sp)
      s₀.mem s₂.mem :=
    (f₁.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..).trans
      (jf₂.mono fun r hr => List.mem_cons_of_mem _ hr)
  obtain dc₂ : ∀ r ∈ oneR (stackArg s₀ 2) :: j0Frame (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₀.sp,
      (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact dcW.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L₀.cs
      · exact dcW.sub_right (Lay.wSub (by decide))
      · exact dcW.sub_right (Lay.wSub (by decide))
      · exact hk₀.c
  obtain dD : ∀ r ∈ oneR (stackArg s₀ 2) :: j0Frame (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₀.sp,
      (⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact data_j0 hd₂₀.ok (sp₂.trans hk₁.sp) r hr
  obtain hc₂ := ciph_keep f₂ dc₂ hR
  obtain hc₃ : ciphOf s₃.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat = ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat := by
    rw [ciph_frame cf₃ (ctx_crFrame L₀ hd₂₀) hR, hc₂]
  obtain hD₂ : bytesAt s₂.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat :=
    bytesAt_frame f₂ dD (by have := (s₀.gpr .a7).isLt; omega_using [])
  obtain hiv : bytesAt s₁.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat = bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnW.sub_right (Lay.wSub (by decide)))
      (by have := (s₀.gpr .a3).isLt; omega_using [])
  obtain haad : bytesAt s₁.mem (s₀.gpr .a4) (s₁.gpr .s10).toNat = bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat := by
    rw [h1.s10]
    exact bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact daW.sub_right (Lay.wSub (by decide)))
      (by have := (s₀.gpr .a5).isLt; omega_using [])
  obtain hj₃ : blockAt s₃.mem (stackArg s₀ 2 + BitVec.ofNat 64 16) =
      j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat) := by
    rw [blockAt_frame cf₃ (by simpa using stp_crFrame L₀ hd₂₀ (d := 0) (k := 16) (by decide)), ← hiv, ← h1.s1]
    exact oa.j
  obtain hD₃ : bytesAt s₃.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat =
      gctr (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
        (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat)))
        (bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat) := by
    have := oc.out
    simp only [setS7, reduceCtorEq, ↓reduceIte] at this
    rw [h1.s11, h1.s2, hc₂, hD₂, hiv] at this
    exact this
  obtain hD₄ : bytesAt s₄.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = bytesAt s₃.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat := by
    refine bytesAt_frame of₄ (fun r hr => ?_) (by have := (s₀.gpr .a7).isLt; omega_using [])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact hstk.buf (by simp)
  obtain hD₅ : bytesAt s₅.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = bytesAt s₄.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat :=
    bytesAt_frame hf₅ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h1.s9]; exact ddt)
      (by have := (s₀.gpr .a7).isLt; omega_using [])
  have ho := ot.out
  simp only [setS7, reduceCtorEq, ↓reduceIte] at ho
  rw [h1.s2, h1.s1, h1.s11, h1.s0, hc₃, hj₃, haad, BitVec.add_zero, ← Proof.Gcm.fullTag_eq] at ho
  rw [h1.s0, h1.s9] at hb₅
  simp only [sealBsRISCV64, sealRISCV64, encryptWith, hm, hD₅, hD₄, hD₃, hb₅, ho]
  refine Prod.ext rfl ?_
  exact List.take_of_length_le (by rw [Spec.Gcm.fullTag, Proof.Gcm.length_gctr, Proof.Cmac.toBytes_length])

/-- The entry of `seal_bitsliced`, from its precondition: `seal`'s, and the
buffer's address at `sp + 8`, whose round keys the entry keeps. -/
theorem sealBsEntry_wp {s₀ : State} (h : sealBsPre s₀) :
    WP isa (.block (oneEntry 16)) s₀ fun s₁ =>
      OneI (s₀.gpr .a0) (stackArg s₀ 2) s₀.sp (s₀.gpr .a1).toNat (s₀.gpr .a2) (s₀.gpr .a3).toNat (s₀.gpr .a4)
        (s₀.gpr .a5) (s₀.gpr .a6) (s₀.gpr .a7) s₁ ∧
      s₁.gpr .s4 = s₀.gpr .a2 ∧ s₁.gpr .s5 = BitVec.ofNat 64 (s₀.gpr .a3).toNat ∧
      s₁.gpr .s9 = stackArg s₀ 0 ∧ Covers [⟨stackArg s₀ 0, 16⟩] s₁.wr ∧
      OD false (s₀.gpr .a0) (stackArg s₀ 2) (s₀.gpr .a6) (s₀.gpr .a6) (s₀.gpr .a7) s₁ ∧
      s₁.mem.readW (s₀.sp + BitVec.ofNat 64 8) 64 = stackArg s₀ 1 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₀.sp + BitVec.ofNat 64 8) 8 ∧
      BkIn (stackArg s₀ 1) (s₀.gpr .a0) (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₀.sp
        (s₀.gpr .a1).toNat s₁.mem (s₀.gpr .a6) (s₀.gpr .a6) (s₀.gpr .a7).toNat s₁ := by
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, dbd, dbW, fc, fn, fa, fd, fW, fsp, hR,
    hstk, ca, wa, ba, hsl⟩ := h
  obtain hk₀ : StkOk (s₀.gpr .a0) (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₀.sp :=
    one_stk hstk (by simp) (by simp)
  obtain hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain hW : Covers [⟨stackArg s₀ 2, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hA : Covers [args s₀ 3] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain hTd : (⟨s₀.sp + BitVec.ofNat 64 0, 8⟩ : Region).Disjoint (oneR (stackArg s₀ 2)) :=
    ((dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).sub_right
      (Region.sub_prefix (show 8 ≤ 8 * 3 by decide))).symm
  refine WP.mono (one1_wp (off := 16) (W := stackArg s₀ 2) (T := stackArg s₀ 0) (.inr rfl) hW wa hstk.1
    (args_in hA (by decide) (i := 2) (by decide)) rfl (args_in hA (by decide) (i := 0) (by decide)) rfl hTd)
    fun s₁ h1 => ?_
  have hk₁ := h1.keeps
  obtain toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  obtain hDw : Covers [⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩] s₁.wr := by
    rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  obtain hDok : DataOk (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₁ (s₀.gpr .a6) (s₀.gpr .a7).toNat :=
    ⟨covers_left hDw, (s₀.gpr .a7).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW,
      by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  obtain hR14 : (s₀.gpr .a1).toNat ≤ 14 := by rcases hR with h | h | h <;> omega_using [h]
  obtain db : (⟨stackArg s₀ 1, 960⟩ : Region).Disjoint ⟨stackArg s₀ 2, 2560⟩ :=
    dbW.sub_left (Region.sub_prefix (by decide))
  obtain f₁ := h1.frame
  refine ⟨⟨s₁.gpr, h1.s2, h1.s1, h1.s0, by rw [h1.s3]; exact toN, by rw [h1.s7]; exact toN,
    h1.s10, h1.s11, one_env h1 hC hW hk₀, ?_, ?_, hDok, h1.aad, h1.dat⟩, h1.s4, by rw [h1.s5]; exact toN, h1.s9, ?_,
    ⟨⟨hDok, hDw, dcd⟩, rfl⟩, ?_, ?_, ?_⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a3).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a5).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  · rw [slot_keep f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dWA.symm.sub_right (Lay.wSub (by decide))).sub_left (Offset.sub s₀.sp (d := 8) (n := 8) (e := 0)
        (k := 24) (by decide) (by decide))]
    rfl
  · rw [hk₁.rd, hk₁.wr]; exact args_in hA (by decide) (i := 1) (by decide)
  · refine ⟨?_, ba, (db.sub_right (Lay.wSub (by decide))), db,
      (stkAll_mem hstk.2.2 (r := ⟨stackArg s₀ 1, 1248⟩) (by simp)).symm.sub_left (Region.sub_prefix (by decide)),
      dbd.sub_left (Region.sub_prefix (by decide)), dbd.sub_left (Region.sub_prefix (by decide)), ?_⟩
    · rw [hk₁.rd, hk₁.wr]
      exact covers_appL (covers_prefix (k := 1248) (covers_mem (by rw [hrd]; simp)) (by decide))
    · refine keysAt_ctx_frame hR f₁ (fun r hr => ?_) (fun r hr => ?_) (keysAt_of_sliced hR14 hsl)
      · simp only [List.mem_singleton] at hr; subst hr; exact db.sub_right (Lay.wSub (by decide))
      · simp only [List.mem_singleton] at hr; subst hr; exact dcW.sub_right (Lay.wSub (by decide))

section
variable {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A D Ln T : BitVec 64} {kb : Addr}

/-- After `oneAad`: the buffer's address in its stack slot, and its round keys. -/
def BkSlot (c W sp : Addr) (R : Nat) (kb : Addr) (D Ln : BitVec 64) (s : State) : Prop :=
  s.mem.readW (sp + BitVec.ofNat 64 8) 64 = kb ∧ InRegions (s.rd ++ s.wr) (sp + BitVec.ofNat 64 8) 8 ∧
    BkIn kb c (W + BitVec.ofNat 64 16) W sp R s.mem D D Ln.toNat s

variable (L : Lay c (W + BitVec.ofNat 64 16) W) (hR : R = 10 ∨ R = 12 ∨ R = 14)
  (hTW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 16⟩) (hsa : sp.toNat % 16 = 0)
  (h8 : ∀ r ∈ RISCV64.j0Frame (W + BitVec.ofNat 64 16) W sp, (⟨sp + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint r)
include L hR hTW hsa h8

/-- `seal_bitsliced` after its entry. -/
theorem sealBsBody_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : CT (fun s => OneT c W sp R Np n Ad A D Ln T s ∧
    s.gpr .s4 = Np ∧ s.gpr .s5 = BitVec.ofNat 64 n ∧ BkSlot c W sp R kb D Ln s)
    (.seq oneAad (.seq (.block (bkLoad 8)) (.seq (oneCryptB true false) (.seq (oneTagB true 0)
      (.seq (.block tagOut) (.block restore)))))) := by
  -- `oneAad`
  refine CT.seq (J := fun s => OneT c W sp R Np n Ad A D Ln T s ∧ OneAbs c W A s ∧ BkSlot c W sp R kb D Ln s)
    ((oneAad_ct L).mono fun s ⟨⟨hO, _⟩, h24, h25, _⟩ => ⟨hO, h24, h25⟩)
    (fun s ⟨hT, h24, h25, k8, i8, hbk⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have hk : StkOk c (W + BitVec.ofNat 64 16) W sp := by rw [← a, ← b, ← d]; exact he.stk'
    refine WP.mono (WP.with_rdwr (oneAad_ok (L.v a b d) (A := Ad) he rfl h24 h25 f (by rw [b, d]; exact hN)
      (by rw [b, d, i]; exact hA) (by rw [d]; exact sa))) fun s' ⟨oa, rd, wr, sp'⟩ => ?_
    have fr := oa.frame
    rw [b, d] at fr
    exact ⟨hT.frame (fun r hr => (he.fr r hr).symm) oa.env rd wr sp' oa.frame
        (fun hd' => by rw [← d]; exact slot_j0 (L.v a b d) he.stk' hd'),
      ⟨blockAt s.mem (V .s2 + BitVec.ofNat 64 240), bytesAt s.mem Ad (V .s10).toNat,
        by rw [← a]; exact oa.hH, by rw [i, length_bytesAt], by rw [← b]; exact oa.abs⟩,
      by rw [slot_keep fr h8]; exact k8, by rw [rd, wr]; exact i8,
      hbk.frame hR fr hbk.j0Frame (ctx_j0Frame L hk) rd wr⟩
  -- `bkLoad 8`
  refine CT.seq (J := fun s => OneIK c W sp R kb Ad A D Ln s ∧ s.gpr .s9 = T ∧ Covers [⟨T, 16⟩] s.wr ∧
      OD false c W D D Ln s ∧ OneAbs c W A s ∧ BkIn kb c (W + BitVec.ofNat 64 16) W sp R s.mem D D Ln.toNat s)
    ?_ (fun s ⟨hT, hab, k8, i8, hbk⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := bkLoad_taint
    exact CT.taint _ (fun s₁ s₂ ⟨⟨⟨_, _, _, _, _, _, _, _, e₁, _⟩, _⟩, _⟩ ⟨⟨⟨_, _, _, _, _, _, _, _, e₂, _⟩, _⟩, _⟩ =>
      ⟨e₁.sp.trans e₂.sp.symm, by simp⟩) hc
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.mono (bkLoad_ok (s := s) (off := 8) (by decide) (by rw [he.sp]; exact hsa) (by decide)
      (by rw [he.sp]; exact i8)) fun s' ⟨b7, g, kp⟩ => ?_
    rw [he.sp, k8] at b7
    obtain he' := he.set7 b7 (fun r hr h7 => g r (by rintro rfl; exact absurd hr (by decide)) h7) kp.sp kp.rd kp.wr
    refine ⟨⟨setS7 V kb, ?_, ?_, ?_, ?_, by simp only [setS7, ↓reduceIte], ?_, ?_, he', hA.of_eq kp.rd kp.wr kp.sp,
      hD.of_eq kp.rd kp.wr kp.sp, by rw [kp.mem]; exact sa, by rw [kp.mem]; exact sd⟩,
      (g .s9 (by decide) (by decide)).trans hT.2.1, by rw [kp.wr]; exact hT.2.2.1,
      hT.2.2.2.of_eq kp.rd kp.wr kp.sp, by simp only [OneAbs, kp.mem]; exact hab,
      by rw [kp.mem]; exact hbk.of_eq kp.rd kp.wr⟩ <;> simp only [setS7, reduceCtorEq, ↓reduceIte] <;> assumption
  -- `oneCryptB true false`
  refine CT.seq (J := fun s => OneIK c W sp R kb Ad A D Ln s ∧ s.gpr .s9 = T ∧ Covers [⟨T, 16⟩] s.wr ∧
      OneAbs c W A s ∧ BkIn kb c (W + BitVec.ofNat 64 16) W sp R s.mem D D Ln.toNat s)
    ((oneCryptB_ct L hR (bs := true) (o := false) (kb := kb) (Dst := D)).mono
      fun s ⟨hK, _, _, hOD, _, bk⟩ => ⟨hK, hOD, Bool.noConfusion, fun _ => ⟨rfl, bk⟩⟩)
    (fun s ⟨hK, h9, hT, hOD, ⟨H, x, hH, hl, hab⟩, hbk⟩ => ?_) ?_
  · have hK' := hK
    obtain ⟨V, a, b, d, e, f, i, k, he, hA, hD, sa, sd⟩ := hK'
    have L' := L.v a b d
    have hd : DataW (V .s2) (V .s1) (V .s0) s D (V .s11).toNat := by rw [a, b, d, k]; exact hOD.1
    refine WP.mono (WP.with_rdwr (oneCryptB_ok L' (bs := true) (o := false) he e hR hd hd.ok rfl
      (fun h => Bool.noConfusion h) (by rw [d]; exact sd) rfl fun _ => by rw [f, a, b, d, k]; exact hbk))
      fun s' ⟨oc, rd, wr, sp'⟩ => ?_
    have fr := oc.frame
    rw [b, d, k] at fr
    refine ⟨OneIK.frame hK (fun r hr => (he.fr r hr).symm) oc.env rd wr sp' oc.frame
        (fun hd' => by rw [← d]; exact slot_crFrame L' hd hd'),
      (oc.env.fr _ (by decide)).trans ((he.fr _ (by decide)).symm.trans h9), by rw [wr]; exact hT,
      ⟨H, x, ?_, hl, ?_⟩, hbk.frame hR fr hbk.crFrame (ctx_crFrame L hOD.1) rd wr⟩
    · rw [← a, blockAt_frame oc.frame (fun r hr => (ctx_crFrame L' hd r hr).sub_left (Lay.ctxSub (by decide)))]
      rw [← a] at hH; exact hH
    · have hx := Nat.mod_lt (x ++ zeros (padLen x.length)).length (show 16 > 0 by decide)
      rw [← b] at hab ⊢
      exact hab.congr (blockAt_frame oc.frame (stp_crFrame L' hd (by decide)))
        (bytesAt_frame oc.frame (stp_crFrame L' hd (by omega_using [])) (by omega_using []))
  -- `oneTagB true 0`
  refine CT.seq (J := fun s => ∃ V : Reg → BitVec 64, V .s0 = W ∧ V .s9 = T ∧ Env V sp s ∧
    Covers [⟨T, 16⟩] s.wr)
    ((oneTagB_ct L (bs := true) (kb := kb) (S' := D) (D' := D) (n' := Ln.toNat) (.inl rfl) hR).mono
      fun s ⟨hK, _, _, _, bk⟩ => ⟨hK, fun _ => ⟨rfl, bk⟩⟩)
    (fun s ⟨hK, h9, hT, ⟨H, x, hH, hl, hab⟩, hbk⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hA, hD, sa, sd⟩ := hK
    refine WP.mono (WP.with_rdwr (oneTagB_ok (L.v a b d) (bs := true) (o := 0) (.inl rfl) (H := H) (a := x) (D := D)
      he e hR (by rw [a]; exact hH) (by rw [i]; exact hl) (by rw [b]; exact hab) (by rw [b, d, k]; exact hD)
      (by rw [d]; exact sd) fun _ => by rw [f, a, b, d]; exact hbk))
      fun s' ⟨ot, _, wr, _⟩ => ⟨V, d, (he.fr _ (by decide)).symm.trans h9, ot.env, by rw [wr]; exact hT⟩
  -- the tag copied out
  refine CT.seq (J := fun s => s.gpr .s0 = W ∧ s.sp = sp) ?_
    (fun s ⟨V, d, i, he, hT⟩ => WP.mono (tagOut_ok he (by rw [i]; exact hT) (by rw [i, d]; exact hTW))
      fun s' ⟨_, _, hg, hk⟩ => ⟨by rw [hg _ (by decide), he.s0, d], by rw [hk.sp, he.sp]⟩) ?_
  · obtain ⟨_, hc⟩ := tagOut_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, d₁, i₁, h₁, _⟩ ⟨_, d₂, i₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => W) sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end

theorem sealBs_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa sealBsRISCV64.pre sealBsRISCV64.pub sealBs := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩ := hq
  have h₁' : sealBsPre σ₁ := h₁
  obtain ⟨_, _, _, dcW, _, _, _, _, _, _, _, dtW, dWA, _, _, fc, _, _, _, fW, _, hR, hstk, ca, wa, _⟩ := h₁'
  obtain hsa : σ₁.sp.toNat % 16 = 0 := hstk.1
  obtain h8 : ∀ r ∈ RISCV64.j0Frame (stackArg σ₁ 2 + BitVec.ofNat 64 16) (stackArg σ₁ 2) σ₁.sp,
      (⟨σ₁.sp + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint r := by
    intro r hr
    refine Region.Disjoint.sub_left ?_ (Offset.sub σ₁.sp (d := 8) (n := 8) (e := 0) (k := 24) (by decide) (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact dWA.symm.sub_right (Lay.wSub (by decide))
    · exact dWA.symm.sub_right (Lay.wSub (by decide))
    · exact dWA.symm.sub_right (Lay.wSub (by decide))
    · exact (stkAll_mem hstk.2.2 (r := args σ₁ 3) (by simp)).symm
  let I₀ : State → Prop := fun s => sealBsPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1 ∧ stackArg s 2 = stackArg σ₁ 2
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm,
    q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm, (qa 1 (by decide)).symm,
    (qa 2 (by decide)).symm⟩, ?_⟩
  refine CT.seq (J := fun s => OneT (σ₁.gpr .a0) (stackArg σ₁ 2) σ₁.sp (σ₁.gpr .a1).toNat (σ₁.gpr .a2)
    (σ₁.gpr .a3).toNat (σ₁.gpr .a4) (σ₁.gpr .a5) (σ₁.gpr .a6) (σ₁.gpr .a7) (stackArg σ₁ 0) s ∧
    s.gpr .s4 = σ₁.gpr .a2 ∧ s.gpr .s5 = BitVec.ofNat 64 (σ₁.gpr .a3).toNat ∧
    BkSlot (σ₁.gpr .a0) (stackArg σ₁ 2) σ₁.sp (σ₁.gpr .a1).toNat (stackArg σ₁ 1) (σ₁.gpr .a6) (σ₁.gpr .a7) s) ?_
    (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2⟩ => ?_)
    (sealBsBody_ct (oneLay fc fW dcW ca wa) hR (dtW.sub_right (Region.sub_prefix (by decide))) hsa h8)
  · -- the entry: its head loads `W` from a public address, the rest saves through it
    let v : Reg → BitVec 64 := fun r => if r = .t1 then stackArg σ₁ 2 else σ₁.gpr r
    rw [oneEntry_eq]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := oneHead16_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, _, _, ea2⟩
      have hA : Covers [args s 3] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hs.1]; simp))
      have hsa : s.sp.toNat % 16 = 0 := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := hs
        exact hk.1
      refine WP.mono (oneA_ok (W := stackArg s 2) (.inr rfl) hsa (args_in hA (by decide) (i := 2) (by decide)) rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea2, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := oneRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  · have := sealBsEntry_wp hs
    rw [ea0, ea1, ea2, e3, e4, e5, e6, e7, e8, e9, e10, esp] at this
    exact WP.mono this fun s' ⟨hO, h24, h25, h20, hT, hOD, k8, i8, hbk⟩ => ⟨⟨hO, h20, hT, hOD⟩, h24, h25, k8, i8, hbk⟩

end VG.Proof.AesGcm.RISCV64
