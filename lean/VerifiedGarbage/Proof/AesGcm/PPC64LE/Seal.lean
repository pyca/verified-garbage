module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFused
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesGcm.PPC64LE

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/Seal.lean`): the entry, `oneAad`, `oneCrypt`, `oneTag 0`
and the tag copied out to `tag` (`seal_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ghashInput fullTag zeros padLen j0 inc32 gctr encryptWith toBytes)
open VG.Proof.Gcm (Absorbed)

/-- The state at `W + 16`, inside the working space `W`. -/
theorem oneLay {c W : Addr} (fc : c.toNat + 256 ≤ 2 ^ 64) (fW : W.toNat + 2560 ≤ 2 ^ 64)
    (dcW : (⟨c, 256⟩ : Region).Disjoint ⟨W, 2560⟩) : Lay c (W + BitVec.ofNat 64 16) W := by
  have sw : (W + BitVec.ofNat 64 16).toNat + 80 ≤ 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have sa : (⟨W + BitVec.ofNat 64 16, 80⟩ : Region).Disjoint ⟨W, 16⟩ := by
    simpa using Lay.w_w (w := W) (a := 16) (n := 80) (d := 0) (k := 16) (.inr (by decide)) (by decide)
      (by decide)
  have sb : (⟨W + BitVec.ofNat 64 16, 80⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 96, 2464⟩ :=
    Lay.w_w (a := 16) (n := 80) (d := 96) (k := 2464) (.inl (by decide)) (by decide) (by decide)
  exact ⟨fc, sw, fW, dcW.sub_right (Lay.wSub (by decide)), dcW, sa, sb⟩

theorem stackArgAddr_0 (s : State) : stackArgAddr s 0 = s.sp + BitVec.ofNat 64 96 := rfl

theorem stackArg_eq (s : State) (i : Nat) :
    stackArg s i = s.mem.readW (s.sp + BitVec.ofNat 64 (32 + 8 * (8 + i))) 64 := rfl

/-- The stack arguments, in a state that may read them. -/
theorem args_in {s : State} {n : Nat} (h : Covers [args s n] (s.rd ++ s.wr)) (hn : n ≤ 3) {i : Nat}
    (hi : i < n) : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (96 + 8 * i)) 8 := by
  have := in_off h (d := 8 * i) (n := 8) (by omega) (by omega)
  rwa [stackArgAddr_0, add_ofNat_assoc] at this

/-- After the entry, the environment. -/
theorem one_env {s₀ s₁ : State} {W T : Addr} (h1 : SO1 W T s₀ s₁)
    (hC : Covers [⟨s₀.gpr .r3, 256⟩] (s₀.rd ++ s₀.wr)) (hW : Covers [⟨W, 2560⟩] s₀.wr) :
    Env s₁.gpr s₀.sp s₁ := by
  have perm : Perm (s₀.gpr .r3) (W + BitVec.ofNat 64 16) W s₁ :=
    (⟨hC, covers_off hW (show 16 + 80 ≤ 2560 by decide) (by decide), hW⟩ :
      Perm (s₀.gpr .r3) (W + BitVec.ofNat 64 16) W s₀).of_eq h1.en.keeps.rd h1.en.keeps.wr
  exact ⟨fun _ _ => rfl, h1.en.keeps.sp, by rw [h1.r29, h1.r30, h1.r31]; exact perm⟩

section
variable {c st w : Addr} (L : Lay c st w)
include L

theorem saved_otFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ otFrame st w o, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.saved_st (d := 0) (k := 48) (by decide)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by omega) (.inl (by omega))
  · exact saved_w (by decide) (.inr (by decide))

end

theorem sealBody_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {sealBody : Prog isa}
    (bodyCorrect : SealFused.BodyCorrect sealBody) {s₀ : State} (h : sealPPC64LE.pre s₀) :
    WP isa (Impl.AesGcm.PPC64LE.SealFused.withBody sealBody) s₀ fun s' => abiPreserved s₀ s' ∧ sealPPC64LE.post s₀ s' := by
  have h' : sealPre s₀ := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, fW, fsp, hR⟩ := h'
  have L₀ := oneLay fc fW dcW
  have hC : Covers [⟨s₀.gpr .r3, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hA : Covers [args s₀ 2] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hTd : (⟨s₀.sp + BitVec.ofNat 64 96, 8⟩ : Region).Disjoint (savedR (stackArg s₀ 1)) :=
    ((dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).sub_right
      (Region.sub_prefix (show 8 ≤ 8 * 2 by decide))).symm
  refine WP.seq (WP.mono (one1_wp (off := 104) (W := stackArg s₀ 1) (T := stackArg s₀ 0) (.inl rfl) hW
    (args_in hA (by decide) (i := 1) (by decide)) rfl (args_in hA (by decide) (i := 0) (by decide)) rfl hTd) fun s₁ h1 => ?_)
  have he₁ := one_env h1 hC hW
  have L := L₀.v h1.r29 h1.r30 h1.r31
  have f₁ := h1.en.frame
  have hk₁ := h1.en.keeps
  -- `oneAad`
  have hH₁ : blockAt s₁.mem (s₁.gpr .r29 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .r3) := by
    rw [h1.r29]; exact ctxH_keep f₁ (ctx_saved L₀)
  have hN : DataOk (s₁.gpr .r30) (s₁.gpr .r31) s₁ (s₀.gpr .r5) (s₀.gpr .r6).toNat := by
    rw [h1.r30, h1.r31]
    exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)), (s₀.gpr .r6).isLt,
      fn, dnW.sub_right (Lay.wSub (by decide)), dnW⟩
  have hAd : DataOk (s₁.gpr .r30) (s₁.gpr .r31) s₁ (s₁.gpr .r21) (s₁.gpr .r22).toNat := by
    rw [h1.r30, h1.r31, h1.r21, h1.r22]
    exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)), (s₀.gpr .r8).isLt,
      fa, daW.sub_right (Lay.wSub (by decide)), daW⟩
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₁ hH₁ h1.r24 (by rw [h1.r25]; exact toN)
    (by rw [h1.r18]; exact toN) hN hAd)) fun s₂ ⟨oa, rd₂, wr₂, _⟩ => ?_)
  -- `oneCrypt`
  have hd₂ : DataW (s₁.gpr .r29) (s₁.gpr .r30) (s₁.gpr .r31) s₂ (s₁.gpr .r27) (s₁.gpr .r23).toNat := by
    rw [h1.r29, h1.r30, h1.r31, h1.r27, h1.r23]
    have hDw : Covers [⟨s₀.gpr .r9, (s₀.gpr .r10).toNat⟩] s₂.wr := by
      rw [wr₂, hk₁.wr, hwr]; exact covers_mem (by simp)
    exact ⟨⟨covers_left hDw, (s₀.gpr .r10).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW⟩, hDw, dcd⟩
  have h28 : s₁.gpr .r28 = BitVec.ofNat 64 (s₀.gpr .r4).toNat := by rw [h1.r28]; exact toN
  have hab₂ : Absorbed s₂.mem (s₁.gpr .r30+16) (s₁.gpr .r30+32)
      (ctxH s₂.mem (s₁.gpr .r29))
      (bytesAt s₁.mem (s₁.gpr .r21) (s₁.gpr .r22).toNat ++
        zeros (padLen (bytesAt s₁.mem (s₁.gpr .r21) (s₁.gpr .r22).toNat).length)) := by
    rw [ctxH_eq,oa.hH]; exact oa.abs
  refine WP.seq (WP.mono (WP.with_rdwr (bodyCorrect L oa.env hd₂ h28 hR
    (length_bytesAt _ _ _).symm hab₂)) fun s₄ ⟨bo,rd₄,wr₄,_⟩ => ?_)
  have hTw : Covers [⟨s₁.gpr .r20,16⟩] s₄.wr := by
    rw [wr₄,wr₂,hk₁.wr,h1.r20,hwr]; exact covers_mem (by simp)
  have hTd' : (⟨s₁.gpr .r20,16⟩ : Region).Disjoint ⟨s₁.gpr .r31,16⟩ := by
    rw [h1.r20,h1.r31]; exact dtW.sub_right (Region.sub_prefix (by decide))
  refine WP.seq (WP.mono (tagOut_ok bo.env hTw hTd') fun s₅ ⟨hb₅,hf₅,g₅,k₅⟩ => ?_)
  have he₅ := bo.env.keep (fun r hr => g₅ r (by revert r; decide)) k₅.sp k₅.rd k₅.wr
  have jf₂ := oa.frame
  rw [h1.r30,h1.r31] at jf₂
  have hd₂₀ : DataW (s₀.gpr .r3) (stackArg s₀ 1+BitVec.ofNat 64 16) (stackArg s₀ 1) s₂
      (s₀.gpr .r9) (s₀.gpr .r10).toNat := by
    rw [← h1.r29,← h1.r30,← h1.r31,← h1.r27,← h1.r23]; exact hd₂
  have sv₂ : SavedAt s₂.mem (s₁.gpr .r31) s₀ := by
    rw [h1.r31]; exact h1.en.saved.frame jf₂ (saved_j0Frame L₀)
  have sv₄ := sv₂.frame bo.frame (SealFused.saved_bodyFrame L hd₂)
  have sv₅ : SavedAt s₅.mem (stackArg s₀ 1) s₀ := by
    have hs := sv₄.frame hf₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h1.r31,h1.r20]; exact (dtW.sub_right (Lay.wSub (by decide))).symm)
    rw [h1.r31] at hs; exact hs
  have e31 : s₅.gpr .r31=stackArg s₀ 1 := (he₅.fr _ (by decide)).trans h1.r31
  refine WP.mono (restore_ok e31 (by have := he₅.perm.w; rw [h1.r31] at this; exact Covers.right this) sv₅
    he₅.sp (fun r hr => by rw [he₅.fr r (by revert hr; revert r; decide)]; exact h1.en.low r hr))
    fun s' ⟨ga,hm,_⟩ => ⟨ga,?_⟩
  have f₂ : Frame (savedR (stackArg s₀ 1) :: j0Frame (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1))
      s₀.mem s₂.mem :=
    (f₁.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..).trans
      (jf₂.mono fun r hr => List.mem_cons_of_mem _ hr)
  have dc₂ : ∀ r ∈ savedR (stackArg s₀ 1) :: j0Frame (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1),
      (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact dcW.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L₀.cs
      · exact dcW.sub_right (Lay.wSub (by decide))
      · exact dcW.sub_right (Lay.wSub (by decide))
  have dD : ∀ r ∈ savedR (stackArg s₀ 1) :: j0Frame (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1),
      (⟨s₀.gpr .r9, (s₀.gpr .r10).toNat⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact data_j0 hd₂₀.ok r hr
  have hc₂ := ciph_keep f₂ dc₂ hR
  change ctxCiph s₂.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat =
    ctxCiph s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat at hc₂
  have hD₂ : bytesAt s₂.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat = bytesAt s₀.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat :=
    bytesAt_frame f₂ dD (by have := (s₀.gpr .r10).isLt; omega)
  have hiv : bytesAt s₁.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat = bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnW.sub_right (Lay.wSub (by decide)))
      (by have := (s₀.gpr .r6).isLt; omega)
  have haad : bytesAt s₁.mem (s₁.gpr .r21) (s₁.gpr .r22).toNat = bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat := by
    rw [h1.r21, h1.r22]
    exact bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact daW.sub_right (Lay.wSub (by decide)))
      (by have := (s₀.gpr .r8).isLt; omega)
  have hD₄ := bo.ciphertext
  have hcb₂ := oa.cb
  change blockAt s₂.mem (s₁.gpr .r30+48)=_ at hcb₂
  rw [hcb₂,h1.r29,h1.r27,h1.r23,hc₂,hD₂,hiv] at hD₄
  have hD₅ : bytesAt s₅.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat =
      bytesAt s₄.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat :=
    bytesAt_frame hf₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h1.r20]; exact ddt)
      (by have := (s₀.gpr .r10).isLt; omega)
  have hH₂ : ctxH s₂.mem (s₁.gpr .r29)=ctxH s₀.mem (s₀.gpr .r3) := by
    rw [ctxH_eq]; exact oa.hH
  have ho := bo.tag
  rw [hH₂,oa.j,h1.r29,h1.r27,h1.r23,h1.r31,hc₂,hiv,haad] at ho
  have hfull := Proof.Gcm.fullTag_eq
    (ctxCiph s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat) (ctxH s₀.mem (s₀.gpr .r3))
    (bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat)
    (bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat)
    (bytesAt s₄.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat)
  simp only [length_bytesAt] at hfull ho
  rw [← hfull,hD₄] at ho
  rw [h1.r31,h1.r20] at hb₅
  simp only [sealPPC64LE,encryptWith,hm,hD₅,hD₄,hb₅,ho]
  refine Prod.ext rfl ?_
  exact List.take_of_length_le (by rw [Spec.Gcm.fullTag,Proof.Gcm.length_gctr,Proof.Cmac.toBytes_length])

theorem seal_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {s₀ : State} (h : sealPPC64LE.pre s₀) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealPPC64LE.post s₀ s' := by
  exact sealBody_wp (sealBody := .seq oneCrypt (oneTag 0))
    (fun L he hd hR hv ha hab => SealFused.smallBody_ok L he hd hR hv ha hab) h

theorem sealFused_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {s₀ : State} (h : sealPPC64LE.pre s₀) :
    WP isa Impl.AesGcm.PPC64LE.SealFused.seal s₀
      fun s' => abiPreserved s₀ s' ∧ sealPPC64LE.post s₀ s' :=
  sealBody_wp (fun L he hd hR hv ha hab => SealFused.body_ok L he hd hR hv ha hab) h

end VG.Proof.AesGcm.PPC64LE
