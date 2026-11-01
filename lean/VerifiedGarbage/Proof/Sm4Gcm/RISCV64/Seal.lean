module

public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.OneShot
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.OneEntry
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamFinish
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_seal`

Untrusted: everything here is checked by Lean. AES-GCM's
(`Proof/AesGcm/RISCV64/Seal.lean`) with SM4's pieces: the entry loads `W`
from the stack argument and keeps the arguments (`one1_wp`), then `oneAad`,
`oneCrypt` and `oneTag 0` run on the state at `W + 16`, and `tagOut`
copies the tag to `tag` (`seal_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov tagOut dataO oneAad)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel stp_crFrame saved_crFrame ciph_keep tagFrame TagOut TagMid tagLens_ok
  tagArgs_ok ctrTag_mk tagCall_ok tag_ok slot_crFrame OC oneCrypt_ok otFrame abs_otSub t_otSub tag_otSub OT
  oneTag_ok SO1 one1_wp one_env saved_otFrame seal_wp sealPre sealRISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput zeros padLen j0 inc32 gctr ctxH encryptWith)
open VG.Spec.Sm4.Gcm (ctxCiph)

/-- The stack below `sp`, for the state at `W + 16`. -/
theorem one_stk3 {s : State} {rs : List Region} (h : stkOk3 s rs) {c W : Addr} (hc : ⟨c, 256⟩ ∈ rs)
    (hw : ⟨W, 2560⟩ ∈ rs) : StkOk c (W + BitVec.ofNat 64 16) W s.sp :=
  ⟨h.buf hc, (h.buf hw).sub_left (Lay.wSub (by decide)), h.buf hw, h.1, by have := h.2.1; omega⟩

/-- After the entry, the environment. -/
theorem one_env {s₀ s₁ : State} {W : Addr} (h1 : SO1 W s₀ s₁)
    (hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr)) (hW : Covers [⟨W, 2560⟩] s₀.wr)
    (hk : StkOk (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₀.sp) :
    Env s₁.gpr s₀.sp s₁ := by
  have perm : Perm (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₁ :=
    (⟨hC, covers_off hW (show 16 + 80 ≤ 2560 by decide) (by decide), hW⟩ :
      Perm (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₀).of_eq h1.keeps.rd h1.keeps.wr
  exact ⟨fun _ _ => rfl, h1.keeps.sp, by rw [h1.s2, h1.s1, h1.s0]; exact perm,
    by rw [h1.s2, h1.s1, h1.s0, h1.keeps.sp]; exact hk⟩

section
variable {c st w : Addr} (L : Lay c st w)
include L

theorem saved_otFrame {sp : Addr} (hbw : (below sp 3232).Disjoint ⟨w, 2560⟩) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ otFrame st w o sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.saved_st (d := 0) (k := 48) (by decide)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by omega) (.inl (by omega))
  · exact saved_w (by decide) (.inr (by decide))
  · exact (hbw.sub_right (Lay.wSub (by decide))).symm

end

theorem seal_wp {s₀ : State} (h : sealRISCV64.pre s₀) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealRISCV64.post s₀ s' := by
  have h' : sealPre s₀ := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, hstk,
    ca, wa⟩ := h'
  have L₀ := oneLay fc fW dcW ca wa
  have hk₀ : StkOk (s₀.gpr .a0) (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0) s₀.sp :=
    one_stk3 hstk (by simp) (by simp)
  have bc₀ : (below s₀.sp 3232).Disjoint ⟨s₀.gpr .a0, 256⟩ := hstk.buf3 (by simp)
  have bw₀ : (below s₀.sp 3232).Disjoint ⟨stackArg s₀ 0, 2560⟩ := hstk.buf3 (by simp)
  have bd₀ : (below s₀.sp 3232).Disjoint ⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩ := hstk.buf3 (by simp)
  have bs₀ : (below s₀.sp 3232).Disjoint ⟨stackArg s₀ 0 + BitVec.ofNat 64 16, 80⟩ :=
    bw₀.sub_right (Lay.wSub (by decide))
  have hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW : Covers [⟨stackArg s₀ 0, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hA : Covers [args s₀ 1] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  refine WP.seq (WP.mono (one1_wp (off := 0) (W := stackArg s₀ 0) (.inl rfl) hW wa hstk.1
    (args_in hA (by decide) (i := 0) (by decide)) rfl) fun s₁ h1 => ?_)
  have he₁ := one_env h1 hC hW hk₀
  have hb₁ : Big s₁.gpr s₀.sp := ⟨hstk.2.1, by rw [h1.s2]; exact bc₀, by rw [h1.s1]; exact bs₀,
    by rw [h1.s0]; exact bw₀⟩
  have L := L₀.v h1.s2 h1.s1 h1.s0
  have f₁ := h1.frame
  have hk₁ := h1.keeps
  have cO : ∀ r ∈ [oneR (stackArg s₀ 0)], (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dcW.sub_right (Lay.wSub (by decide))
  -- `oneAad`
  have hH₁ : blockAt s₁.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
    rw [h1.s2]; exact ctxH_keep f₁ cO
  have hN : DataOk (s₁.gpr .s1) (s₁.gpr .s0) s₁ (s₀.gpr .a1) (s₀.gpr .a2).toNat := by
    rw [h1.s1, h1.s0]
    exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)), (s₀.gpr .a2).isLt,
      fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  have hAd : DataOk (s₁.gpr .s1) (s₁.gpr .s0) s₁ (s₀.gpr .a3) (s₁.gpr .s10).toNat := by
    rw [h1.s1, h1.s0, h1.s10]
    exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)), (s₀.gpr .a4).isLt,
      fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₁ hH₁ h1.s4 (by rw [h1.s5]; exact toN)
    (by rw [h1.s7]; exact toN) hN hAd (by rw [h1.s0]; exact h1.aad))) fun s₂ ⟨oa, rd₂, wr₂, sp₂⟩ => ?_)
  -- `oneCrypt`
  have hd₂ : DataW (s₁.gpr .s2) (s₁.gpr .s1) (s₁.gpr .s0) s₂ (s₀.gpr .a5) (s₁.gpr .s11).toNat := by
    rw [h1.s2, h1.s1, h1.s0, h1.s11]
    have hDw : Covers [⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩] s₂.wr := by
      rw [wr₂, hk₁.wr, hwr]; exact covers_mem (by simp)
    exact ⟨⟨covers_left hDw, (s₀.gpr .a6).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW,
      by rw [sp₂, hk₁.sp]; exact hstk.buf (by simp)⟩, hDw, dcd⟩
  have hD₂s : s₂.mem.readW (s₁.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a5 := by
    rw [slot_keep oa.frame (slot_j0 L he₁.stk' (by decide)), h1.s0]; exact h1.dat
  refine WP.seq (WP.mono (WP.with_rdwr (oneCrypt_ok L hb₁ oa.env hd₂ (by rw [h1.s11]; exact bd₀) hD₂s oa.cb))
    fun s₃ ⟨oc, rd₃, wr₃, sp₃⟩ => ?_)
  -- `oneTag 0`
  have hH₃ : blockAt s₃.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
    rw [blockAt_frame oc.frame (fun r hr => (ctx_crFrame L hb₁ hd₂ r hr).sub_left (Lay.ctxSub (by decide)))]
    exact oa.hH
  have hb := Nat.mod_lt (bytesAt s₁.mem (s₀.gpr .a3) (s₁.gpr .s10).toNat ++
    zeros (padLen (bytesAt s₁.mem (s₀.gpr .a3) (s₁.gpr .s10).toNat).length)).length (show 16 > 0 by decide)
  have hab₃ := oa.abs.congr (blockAt_frame oc.frame (stp_crFrame hb₁.st hd₂ (by decide)))
    (bytesAt_frame oc.frame (stp_crFrame hb₁.st hd₂ (by omega)) (by omega))
  have hD₃s : s₃.mem.readW (s₁.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a5 := by
    rw [slot_keep oc.frame (slot_crFrame L hb₁ hd₂ (by decide))]; exact hD₂s
  refine WP.seq (WP.mono (WP.with_rdwr (oneTag_ok L hb₁ (o := 0) (.inl rfl) oc.env hH₃
    (length_bytesAt _ _ _).symm hab₃ (hd₂.ok.of_eq rd₃ wr₃ sp₃) hD₃s)) fun s₄ ⟨ot, rd₄, wr₄, _⟩ => ?_)
  -- the tag copied out
  have hTw : Covers [⟨s₁.gpr .s9, 16⟩] s₄.wr := by
    rw [wr₄, wr₃, wr₂, hk₁.wr, h1.s9, hwr]; exact covers_mem (by simp)
  have hTd' : (⟨s₁.gpr .s9, 16⟩ : Region).Disjoint ⟨s₁.gpr .s0, 16⟩ := by
    rw [h1.s9, h1.s0]; exact dtW.sub_right (Region.sub_prefix (by decide))
  refine WP.seq (WP.mono (tagOut_ok ot.env hTw hTd') fun s₅ ⟨hb₅, hf₅, g₅, k₅⟩ => ?_)
  have he₅ := ot.env.keep (fun r hr => g₅ r (by revert r; decide)) k₅.sp k₅.rd k₅.wr
  have of₄ := ot.frame
  rw [h1.s1, h1.s0] at of₄
  have cf₃ := oc.frame
  rw [h1.s1, h1.s11] at cf₃
  have jf₂ := oa.frame
  rw [h1.s1, h1.s0] at jf₂
  have hd₂₀ : DataW (s₀.gpr .a0) (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0) s₂ (s₀.gpr .a5)
      (s₀.gpr .a6).toNat := by rw [← h1.s2, ← h1.s1, ← h1.s0, ← h1.s11]; exact hd₂
  have sv₁ : SavedAt s₁.mem (stackArg s₀ 0) s₀ := h1.saved
  have sv₅ : SavedAt s₅.mem (stackArg s₀ 0) s₀ :=
    (((sv₁.frame jf₂ (saved_j0Frame L₀ hk₀)).frame cf₃ (saved_crFrame L₀ bw₀ hd₂₀)).frame of₄
      (saved_otFrame L₀ bw₀ (.inl rfl))).frame (by rw [h1.s9] at hf₅; exact hf₅) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dtW.sub_right (Lay.wSub (by decide))).symm)
  have e31 : s₅.gpr .s0 = stackArg s₀ 0 := (he₅.fr _ (by decide)).trans h1.s0
  refine WP.mono (restore_ok e31 wa (by have := he₅.perm.w; rw [h1.s0] at this; exact Covers.right this) sv₅
    he₅.sp) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  -- the results
  have f₂ : Frame (oneR (stackArg s₀ 0) :: j0Frame (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0) s₀.sp)
      s₀.mem s₂.mem :=
    (f₁.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..).trans
      (jf₂.mono fun r hr => List.mem_cons_of_mem _ hr)
  have dc₂ : ∀ r ∈ oneR (stackArg s₀ 0) :: j0Frame (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0) s₀.sp,
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
  have dD : ∀ r ∈ oneR (stackArg s₀ 0) :: j0Frame (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0) s₀.sp,
      (⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact data_j0 hd₂₀.ok (sp₂.trans hk₁.sp) r hr
  have hc₂ := ciph_keep f₂ dc₂
  have hc₃ : ciphOf s₃.mem (s₀.gpr .a0) = ctxCiph s₀.mem (s₀.gpr .a0) := by
    rw [ciph_frame cf₃ (ctx_crFrame' L₀ bc₀ hd₂₀), hc₂]
  have hD₂ : bytesAt s₂.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat :=
    bytesAt_frame f₂ dD (by have := (s₀.gpr .a6).isLt; omega)
  have hiv : bytesAt s₁.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat = bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnW.sub_right (Lay.wSub (by decide)))
      (by have := (s₀.gpr .a2).isLt; omega)
  have haad : bytesAt s₁.mem (s₀.gpr .a3) (s₁.gpr .s10).toNat = bytesAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat := by
    rw [h1.s10]
    exact bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact daW.sub_right (Lay.wSub (by decide)))
      (by have := (s₀.gpr .a4).isLt; omega)
  have hj₃ : blockAt s₃.mem (stackArg s₀ 0 + BitVec.ofNat 64 16) =
      j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat) := by
    rw [blockAt_frame cf₃ (by simpa using stp_crFrame bs₀ hd₂₀ (d := 0) (k := 16) (by decide)), ← hiv, ← h1.s1]
    exact oa.j
  have hD₃ : bytesAt s₃.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat =
      gctr (ctxCiph s₀.mem (s₀.gpr .a0))
        (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat)))
        (bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat) := by
    have := oc.out
    rw [h1.s11, h1.s2, hc₂, hD₂, hiv] at this
    exact this
  have hD₄ : bytesAt s₄.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = bytesAt s₃.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat := by
    refine bytesAt_frame of₄ (fun r hr => ?_) (by have := (s₀.gpr .a6).isLt; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact bd₀.symm
  have hD₅ : bytesAt s₅.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = bytesAt s₄.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat :=
    bytesAt_frame hf₅ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h1.s9]; exact ddt)
      (by have := (s₀.gpr .a6).isLt; omega)
  have ho := ot.out
  rw [h1.s2, h1.s1, h1.s11, h1.s0, hc₃, hj₃, haad, BitVec.add_zero, ← Proof.Gcm.fullTag_eq] at ho
  rw [h1.s0, h1.s9] at hb₅
  simp only [sealRISCV64, encryptWith, hm, hD₅, hD₄, hD₃, hb₅, ho]
  refine Prod.ext rfl ?_
  exact List.take_of_length_le (by rw [Spec.Gcm.fullTag, Proof.Gcm.length_gctr, Proof.Cmac.toBytes_length])

end VG.Proof.Sm4Gcm.RISCV64
