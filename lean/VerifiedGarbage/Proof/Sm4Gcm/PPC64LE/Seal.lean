module

public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.OneShot
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.OneEntry
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_seal`

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/Seal.lean`), with SM4's counter mode, which uses the
working space past AES-GCM's 2560 bytes: the entry, `oneAad`, `oneCrypt`,
`oneTag 0` and the tag copied out to `tag` (`seal_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Proof.AesGcm.PPC64LE (Env Lay Perm DataW DataOk SavedAt savedR restore_ok covers_mem covers_left
  covers_off covers_prefix bytesAt_frame blockAt_frame ctx_saved ctxH_keep saved_w Lay.saved_st WP.with_rdwr
  tagOut_ok saved_j0Frame data_j0 oneAad_ok oneLay args_in j0Frame length_bytesAt)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ghashInput fullTag zeros padLen j0 inc32 gctr encryptWith toBytes)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed)

/-- After the entry, the environment. -/
theorem one_env {s₀ s₁ : State} {W : Addr} (h1 : SO1 W s₀ s₁)
    (hC : Covers [⟨s₀.gpr .r3, 256⟩] (s₀.rd ++ s₀.wr)) (hW : Covers [⟨W, 2560⟩] s₀.wr) :
    Env s₁.gpr s₀.sp s₁ := by
  have perm : Perm (s₀.gpr .r3) (W + BitVec.ofNat 64 16) W s₁ :=
    (⟨hC, covers_off hW (show 16 + 80 ≤ 2560 by decide) (by decide), hW⟩ :
      Perm (s₀.gpr .r3) (W + BitVec.ofNat 64 16) W s₀).of_eq h1.en.keeps.rd h1.en.keeps.wr
  exact ⟨fun _ _ => rfl, h1.en.keeps.sp, by rw [h1.r29, h1.r30, h1.r31]; exact perm⟩

/-- SM4's working space, past the state at `W + 16`. -/
theorem oneX {c W : Addr} (fW : W.toNat + scrBytes ≤ 2 ^ 64) (dcW : (⟨c, 256⟩ : Region).Disjoint ⟨W, scrBytes⟩) :
    XOk c (W + BitVec.ofNat 64 16) W :=
  ⟨fW, dcW.sub_right (VG.Offset.sub_base _ (by decide)),
    VG.Offset.disjoint _ (.inl (by decide)) (by decide) (by simp only [sO, sBytes, scrBytes] at fW ⊢; omega)⟩

section
variable {c st w : Addr} (L : Lay c st w) (X : XOk c st w)
include L X

theorem saved_otFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ otFrame st w o, (savedR w).Disjoint r := by
  have hf : w.toNat + 5824 ≤ 2 ^ 64 := X.fit
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.saved_st (d := 0) (k := 48) (by decide)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by omega) (.inl (by omega))
  · exact saved_w (by decide) (.inr (by decide))
  · exact VG.Offset.disjoint _ (.inl (by simp only [sO]; omega)) (by omega) (by simp only [sO, sBytes]; omega)

end

theorem seal_wp {s₀ : State} (h : sealPPC64LE.pre s₀) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealPPC64LE.post s₀ s' := by
  have h' : sealPre s₀ := h
  obtain ⟨hrd, hwr, dcd, dcX, dnd, dnX, dad, daX, ddt, ddX, ddA, dtX, dXA, fc, fn, fa, fd, -, fX, fsp⟩ := h'
  have sub : Region.Sub ⟨stackArg s₀ 0, 2560⟩ ⟨stackArg s₀ 0, scrBytes⟩ := Region.sub_prefix (by decide)
  have dcW := dcX.sub_right sub
  have dnW := dnX.sub_right sub
  have daW := daX.sub_right sub
  have ddW := ddX.sub_right sub
  have dtW := dtX.sub_right sub
  have fX' : (stackArg s₀ 0).toNat + 5824 ≤ 2 ^ 64 := fX
  have L₀ := oneLay fc (by omega) dcW
  have X₀ := oneX fX dcX
  have hC : Covers [⟨s₀.gpr .r3, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW' : Covers [⟨stackArg s₀ 0, scrBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hW : Covers [⟨stackArg s₀ 0, 2560⟩] s₀.wr := covers_prefix hW' (by decide)
  have hXw : Covers [xR (stackArg s₀ 0)] s₀.wr := covers_off hW' (by decide) (by decide)
  have hA : Covers [args s₀ 1] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  refine WP.seq (WP.mono (one1_wp (off := 96) (W := stackArg s₀ 0) (.inl rfl) hW
    (args_in hA (by decide) (i := 0) (by decide)) rfl) fun s₁ h1 => ?_)
  have he₁ := one_env h1 hC hW
  have L := L₀.v h1.r29 h1.r30 h1.r31
  have X : XOk (s₁.gpr .r29) (s₁.gpr .r30) (s₁.gpr .r31) := by rw [h1.r29, h1.r30, h1.r31]; exact X₀
  have f₁ := h1.en.frame
  have hk₁ := h1.en.keeps
  -- `oneAad`
  have hH₁ : blockAt s₁.mem (s₁.gpr .r29 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .r3) := by
    rw [h1.r29]; exact ctxH_keep f₁ (ctx_saved L₀)
  have hN : DataOk (s₁.gpr .r30) (s₁.gpr .r31) s₁ (s₀.gpr .r4) (s₀.gpr .r5).toNat := by
    rw [h1.r30, h1.r31]
    exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)), (s₀.gpr .r5).isLt,
      fn, dnW.sub_right (Lay.wSub (by decide)), dnW⟩
  have hAd : DataOk (s₁.gpr .r30) (s₁.gpr .r31) s₁ (s₁.gpr .r21) (s₁.gpr .r22).toNat := by
    rw [h1.r30, h1.r31, h1.r21, h1.r22]
    exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)), (s₀.gpr .r7).isLt,
      fa, daW.sub_right (Lay.wSub (by decide)), daW⟩
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₁ hH₁ h1.r24 (by rw [h1.r25]; exact toN)
    (by rw [h1.r18]; exact toN) hN hAd)) fun s₂ ⟨oa, rd₂, wr₂, _⟩ => ?_)
  -- `oneCrypt`
  have hd₂ : DataW (s₁.gpr .r29) (s₁.gpr .r30) (s₁.gpr .r31) s₂ (s₁.gpr .r27) (s₁.gpr .r23).toNat := by
    rw [h1.r29, h1.r30, h1.r31, h1.r27, h1.r23]
    have hDw : Covers [⟨s₀.gpr .r8, (s₀.gpr .r9).toNat⟩] s₂.wr := by
      rw [wr₂, hk₁.wr, hwr]; exact covers_mem (by simp)
    exact ⟨⟨covers_left hDw, (s₀.gpr .r9).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW⟩, hDw, dcd⟩
  have hxw₂ : Covers [xR (s₁.gpr .r31)] s₂.wr := by rw [wr₂, hk₁.wr, h1.r31]; exact hXw
  have hdx : (⟨s₁.gpr .r27, (s₁.gpr .r23).toNat⟩ : Region).Disjoint (xR (s₁.gpr .r31)) := by
    rw [h1.r27, h1.r23, h1.r31]; exact ddX.sub_right (VG.Offset.sub_base _ (by decide))
  refine WP.seq (WP.mono (WP.with_rdwr (oneCrypt_ok L X oa.env hd₂ hxw₂ hdx oa.cb))
    fun s₃ ⟨oc, rd₃, wr₃, _⟩ => ?_)
  -- `oneTag 0`
  have hH₃ : blockAt s₃.mem (s₁.gpr .r29 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .r3) := by
    rw [blockAt_frame oc.frame (fun r hr => (ctx_crFrame L X hd₂ r hr).sub_left (Lay.ctxSub (by decide)))]
    exact oa.hH
  have hb := Nat.mod_lt (bytesAt s₁.mem (s₁.gpr .r21) (s₁.gpr .r22).toNat ++
    zeros (padLen (bytesAt s₁.mem (s₁.gpr .r21) (s₁.gpr .r22).toNat).length)).length (show 16 > 0 by decide)
  have hab₃ := oa.abs.congr (blockAt_frame oc.frame (stp_crFrame X hd₂ (by decide)))
    (bytesAt_frame oc.frame (stp_crFrame X hd₂ (by omega)) (by omega))
  refine WP.seq (WP.mono (WP.with_rdwr (oneTag_ok L X (o := 0) (.inl rfl) oc.env (by rw [wr₃]; exact hxw₂) hH₃
    (length_bytesAt _ _ _).symm hab₃ (hd₂.ok.of_eq rd₃ wr₃))) fun s₄ ⟨ot, rd₄, wr₄, _⟩ => ?_)
  -- the tag copied out
  have hTw : Covers [⟨s₁.gpr .r20, 16⟩] s₄.wr := by
    rw [wr₄, wr₃, wr₂, hk₁.wr, h1.r20, hwr]; exact covers_mem (by simp)
  have hTd' : (⟨s₁.gpr .r20, 16⟩ : Region).Disjoint ⟨s₁.gpr .r31, 16⟩ := by
    rw [h1.r20, h1.r31]; exact dtW.sub_right (Region.sub_prefix (by decide))
  refine WP.seq (WP.mono (tagOut_ok ot.env hTw hTd') fun s₅ ⟨hb₅, hf₅, g₅, k₅⟩ => ?_)
  have he₅ := ot.env.keep (fun r hr => g₅ r (by revert r; decide)) k₅.sp k₅.rd k₅.wr
  have of₄ := ot.frame
  rw [h1.r30, h1.r31] at of₄
  have cf₃ := oc.frame
  rw [h1.r30, h1.r31, h1.r27, h1.r23] at cf₃
  have jf₂ := oa.frame
  rw [h1.r30, h1.r31] at jf₂
  have hd₂₀ : DataW (s₀.gpr .r3) (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0) s₂ (s₀.gpr .r8)
      (s₀.gpr .r9).toNat := by rw [← h1.r29, ← h1.r30, ← h1.r31, ← h1.r27, ← h1.r23]; exact hd₂
  have sv₅ : SavedAt s₅.mem (stackArg s₀ 0) s₀ :=
    (((h1.en.saved.frame jf₂ (saved_j0Frame L₀)).frame cf₃ (saved_crFrame L₀ X₀ hd₂₀)).frame of₄
      (saved_otFrame L₀ X₀ (.inl rfl))).frame (by rw [h1.r20] at hf₅; exact hf₅) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dtW.sub_right (Lay.wSub (by decide))).symm)
  have e31 : s₅.gpr .r31 = stackArg s₀ 0 := (he₅.fr _ (by decide)).trans h1.r31
  refine WP.mono (restore_ok e31 (by have := he₅.perm.w; rw [h1.r31] at this; exact Covers.right this) sv₅
    he₅.sp (fun r hr => by rw [he₅.fr r (by revert hr; revert r; decide)]; exact h1.en.low r hr))
    fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  -- the results
  have f₂ : Frame (savedR (stackArg s₀ 0) :: j0Frame (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0))
      s₀.mem s₂.mem :=
    (f₁.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..).trans
      (jf₂.mono fun r hr => List.mem_cons_of_mem _ hr)
  have dc₂ : ∀ r ∈ savedR (stackArg s₀ 0) :: j0Frame (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0),
      (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact dcW.sub_right (Lay.wSub (by decide))
    · simp only [j0Frame, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L₀.cs
      · exact dcW.sub_right (Lay.wSub (by decide))
      · exact dcW.sub_right (Lay.wSub (by decide))
  have dD : ∀ r ∈ savedR (stackArg s₀ 0) :: j0Frame (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0),
      (⟨s₀.gpr .r8, (s₀.gpr .r9).toNat⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact data_j0 hd₂₀.ok r hr
  have hc₂ := ciph_keep f₂ dc₂
  have hc₃ : ciphOf s₃.mem (s₀.gpr .r3) = ctxCiph s₀.mem (s₀.gpr .r3) := by
    rw [ciph_frame cf₃ (ctx_crFrame' L₀ X₀ hd₂₀), hc₂]
  have hD₂ : bytesAt s₂.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat :=
    bytesAt_frame f₂ dD (by have := (s₀.gpr .r9).isLt; omega)
  have hiv : bytesAt s₁.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat = bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnW.sub_right (Lay.wSub (by decide)))
      (by have := (s₀.gpr .r5).isLt; omega)
  have haad : bytesAt s₁.mem (s₁.gpr .r21) (s₁.gpr .r22).toNat = bytesAt s₀.mem (s₀.gpr .r6) (s₀.gpr .r7).toNat := by
    rw [h1.r21, h1.r22]
    exact bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact daW.sub_right (Lay.wSub (by decide)))
      (by have := (s₀.gpr .r7).isLt; omega)
  have hj₃ : blockAt s₃.mem (stackArg s₀ 0 + BitVec.ofNat 64 16) =
      j0 (ctxH s₀.mem (s₀.gpr .r3)) (bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat) := by
    rw [blockAt_frame cf₃ (by simpa using stp_crFrame X₀ hd₂₀ (d := 0) (k := 16) (by decide)), ← hiv, ← h1.r30]
    exact oa.j
  have hD₃ : bytesAt s₃.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat =
      gctr (ctxCiph s₀.mem (s₀.gpr .r3))
        (inc32 (j0 (ctxH s₀.mem (s₀.gpr .r3)) (bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat)))
        (bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat) := by
    have := oc.out
    rw [h1.r27, h1.r23, h1.r29, hc₂, hD₂, hiv] at this
    exact this
  have hD₄ : bytesAt s₄.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = bytesAt s₃.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat := by
    refine bytesAt_frame of₄ (fun r hr => ?_) (by have := (s₀.gpr .r9).isLt; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddX.sub_right (VG.Offset.sub_base _ (by decide))
  have hD₅ : bytesAt s₅.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = bytesAt s₄.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat :=
    bytesAt_frame hf₅ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h1.r20]; exact ddt)
      (by have := (s₀.gpr .r9).isLt; omega)
  have ho := ot.out
  rw [h1.r29, h1.r30, h1.r27, h1.r23, h1.r31, hc₃, hj₃, haad, BitVec.add_zero, ← Proof.Gcm.fullTag_eq] at ho
  rw [h1.r31, h1.r20] at hb₅
  simp only [sealPPC64LE, encryptWith, hm, hD₅, hD₄, hD₃, hb₅, ho]
  refine Prod.ext rfl ?_
  exact List.take_of_length_le (by rw [Spec.Gcm.fullTag, Proof.Gcm.length_gctr, Proof.Cmac.toBytes_length])

end VG.Proof.Sm4Gcm.PPC64LE
