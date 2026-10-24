module

public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Gcm.Ctr
public import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/StreamCrypt.lean`), with SM4's `crypt`: the entry saves our caller's
registers and keeps the arguments in `r19`–`r30` (`sc1_wp`); `encrypt` runs
`crypt` on the data and then absorbs what it wrote (`textAbsorb`), `decrypt`
absorbs the data first; both keep `J₀` (`enc_run`, `dec_run`), which is a
state for the text so far followed by the new text (`streamEncrypt_wp`,
`streamDecrypt_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov textArgs textAbsorb)
open VG.Proof.AesGcm.PPC64LE (Env Lay Perm DataW DataOk Entered SavedAt savedR save_ok restore_ok covers_mem
  covers_left covers_prefix covers_off bytesAt_frame blockAt_frame textArgs_ok textAbsorb_ok taFrame
  stp_taFrame stp_saved ctx_saved ctx_taFrame data_taFrame data_saved saved_taFrame ctxH_keep saved_w
  length_bytesAt toNat_mod16 WP.forall_det WP.with_rdwr Lay.saved_st)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ghashInput gctr inc32 j0)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- After the entry, from `s₀`. -/
structure SC1 (s₀ s₁ : State) : Prop where
  en : Entered s₀ (s₀.gpr .r9) s₁
  r31 : s₁.gpr .r31 = s₀.gpr .r9
  r30 : s₁.gpr .r30 = s₀.gpr .r4
  r29 : s₁.gpr .r29 = s₀.gpr .r3
  r23 : s₁.gpr .r23 = s₀.gpr .r6
  r22 : s₁.gpr .r22 = s₀.gpr .r5
  r20 : s₁.gpr .r20 = s₀.gpr .r7
  r19 : s₁.gpr .r19 = s₀.gpr .r8
  r28 : s₁.gpr .r28 = s₀.gpr .r10

theorem sc1_wp {s₀ : State} (hW : Covers [⟨s₀.gpr .r9, 2560⟩] s₀.wr) :
    WP isa (.block cryptEntry) s₀ (SC1 s₀) := by
  refine WP.block_append (WP.mono (save_ok (b := .r9) (by decide) hW) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e3 : s₁.gpr .r3 = s₀.gpr .r3 := hg _ (by decide) (by decide)
  have e4 : s₁.gpr .r4 = s₀.gpr .r4 := hg _ (by decide) (by decide)
  have e5 : s₁.gpr .r5 = s₀.gpr .r5 := hg _ (by decide) (by decide)
  have e6 : s₁.gpr .r6 = s₀.gpr .r6 := hg _ (by decide) (by decide)
  have e7 : s₁.gpr .r7 = s₀.gpr .r7 := hg _ (by decide) (by decide)
  have e8 : s₁.gpr .r8 = s₀.gpr .r8 := hg _ (by decide) (by decide)
  have e10 : s₁.gpr .r10 = s₀.gpr .r10 := hg _ (by decide) (by decide)
  crun [mov, BitVec.or_self, e3, e4, e5, e6, e7, e8, e10, h31]
  refine ⟨⟨fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hg],
    ⟨hk.rd, hk.wr, hk.sp, hk.lr⟩, hsv, hf⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [h31]

section
variable {s₀ : State} (h : streamCryptPre s₀)
include h

theorem scLay : Lay (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r9) := by
  obtain ⟨-, -, dcs, -, dcw, -, dsw, -, fc, fs, -, fw, -⟩ := h
  have fw' : (s₀.gpr .r9).toNat + 2560 ≤ 2 ^ 64 := fw
  exact Lay.of fc fs (by omega) dcs (dcw.sub_right (Region.sub_prefix (by decide)))
    (dsw.sub_right (Region.sub_prefix (by decide)))

theorem scX : XOk (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r9) (s₀.gpr .r10) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, dcx, dsx, -, dwx, fx⟩ := h
  exact ⟨fx, dcx, dsx, dwx⟩

theorem sc_W' : Covers [⟨s₀.gpr .r9, scrBytes⟩] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

theorem sc_W : Covers [⟨s₀.gpr .r9, 2560⟩] s₀.wr := covers_prefix (sc_W' h) (by decide)

theorem sc_X : Covers [xR (s₀.gpr .r10)] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

/-- The environment after the entry. -/
theorem sc_env {s₁ : State} (h1 : SC1 s₀ s₁) : Env s₁.gpr s₀.sp s₁ := by
  obtain ⟨hrd, hwr, -⟩ := h
  have perm : Perm (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r9) s₁ :=
    (⟨covers_mem (by rw [hrd]; simp), covers_mem (by rw [hwr]; simp),
      covers_prefix (covers_mem (r := ⟨s₀.gpr .r9, scrBytes⟩) (by rw [hwr]; simp)) (by decide)⟩ :
      Perm (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r9) s₀).of_eq h1.en.keeps.rd h1.en.keeps.wr
  exact ⟨fun _ _ => rfl, h1.en.keeps.sp, by rw [h1.r29, h1.r30, h1.r31]; exact perm⟩

/-- The data, as `crypt` needs it. -/
theorem sc_dataW {s : State} (hwr' : s.wr = s₀.wr) :
    DataW (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r9) s (s₀.gpr .r7) (s₀.gpr .r8).toNat := by
  obtain ⟨-, hwr, -, dcd, -, dsd, -, ddw, -, -, fd, -, -⟩ := h
  have hD : Covers [⟨s₀.gpr .r7, (s₀.gpr .r8).toNat⟩] s.wr := by rw [hwr', hwr]; exact covers_mem (by simp)
  exact ⟨⟨covers_left hD, (s₀.gpr .r8).isLt, fd, dsd.symm, ddw.sub_right (Region.sub_prefix (by decide))⟩, hD, dcd⟩

/-- The data are apart from SM4's working space. -/
theorem sc_dx : (⟨s₀.gpr .r7, (s₀.gpr .r8).toNat⟩ : Region).Disjoint (xR (s₀.gpr .r10)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ddx, -⟩ := h
  exact ddx

end

section
variable {c st w x : Addr} (L : Lay c st w) (X : XOk c st w x)
include L X

omit L in
theorem stp_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW c st w s D n) {d k : Nat} (h1 : d + k ≤ 48) :
    ∀ r ∈ crFrame st x D n, (⟨st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.st.sub_right (Lay.stSub (by omega))).symm
  · exact Lay.st_st (.inl h1) (by omega) (by decide)
  · exact X.sx.sub_left (Lay.stSub (by omega))

theorem ctx_crFrame' {s : State} {D : Addr} {n : Nat} (hd : DataW c st w s D n) :
    ∀ r ∈ crFrame st x D n, (⟨c, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hd.ctx
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact X.cx

theorem saved_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW c st w s D n) :
    ∀ r ∈ crFrame st x D n, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact L.saved_st (by decide)
  · exact X.wx.sub_left (Lay.wSub (by decide))

end

theorem ciph_keep {c : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨c, 256⟩ : Region).Disjoint r) : ciphOf m' c = ctxCiph m c := ciph_frame hf hd

/-- What `encrypt` (or `decrypt`) does, for the counter block `icb`, the
additional data `a` and the text `ct` so far (only their lengths matter to
the code). -/
structure EncOut (s₀ : State) (icb : Block) (a ct : List Byte) (dec : Bool) (s : State) : Prop where
  ctr : Ctr s₀.mem (s₀.gpr .r4 + BitVec.ofNat 64 48) (s₀.gpr .r4 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .r3)) icb ct.length →
    Ctr s.mem (s₀.gpr .r4 + BitVec.ofNat 64 48) (s₀.gpr .r4 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .r3)) icb (ct.length + (s₀.gpr .r8).toNat)
  out : Ctr s₀.mem (s₀.gpr .r4 + BitVec.ofNat 64 48) (s₀.gpr .r4 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .r3)) icb ct.length →
    bytesAt s.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat =
      xorKs (ctxCiph s₀.mem (s₀.gpr .r3)) icb ct.length (bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat)
  abs : Ctr s₀.mem (s₀.gpr .r4 + BitVec.ofNat 64 48) (s₀.gpr .r4 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .r3)) icb ct.length →
    Absorbed s₀.mem (s₀.gpr .r4 + BitVec.ofNat 64 16) (s₀.gpr .r4 + BitVec.ofNat 64 32)
      (ctxH s₀.mem (s₀.gpr .r3)) (ghashInput a ct) →
    Absorbed s.mem (s₀.gpr .r4 + BitVec.ofNat 64 16) (s₀.gpr .r4 + BitVec.ofNat 64 32)
      (ctxH s₀.mem (s₀.gpr .r3))
      (ghashInput a (ct ++ if dec then bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat else
        xorKs (ctxCiph s₀.mem (s₀.gpr .r3)) icb ct.length (bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat)))
  j : blockAt s.mem (s₀.gpr .r4) = blockAt s₀.mem (s₀.gpr .r4)

theorem enc_run {s₀ : State} (h : streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (s₀.gpr .r5).toNat % 16) (hP : (s₀.gpr .r6).toNat = ct.length) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct false s' := by
  have L₀ := scLay h
  have X₀ := scX h
  refine WP.seq (WP.block_append (WP.mono (sc1_wp (sc_W h)) fun s₁ h1 => ?_))
  have he₁ := sc_env h h1
  have L := L₀.v h1.r29 h1.r30 h1.r31
  have X : XOk (s₁.gpr .r29) (s₁.gpr .r30) (s₁.gpr .r31) (s₁.gpr .r28) := by rw [h1.r29, h1.r30, h1.r31, h1.r28]; exact X₀
  refine WP.mono textArgs_ok fun s₂ ⟨h24, h25, h26, hg₂, hk₂⟩ => ?_
  have he₂ : Env s₁.gpr s₀.sp s₂ := he₁.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  have hd₂₀ := sc_dataW h (s := s₂) (hk₂.wr.trans h1.en.keeps.wr)
  have hd₂ : DataW (s₁.gpr .r29) (s₁.gpr .r30) (s₁.gpr .r31) s₂ (s₁.gpr .r20) (s₁.gpr .r19).toNat := by
    rw [h1.r29, h1.r30, h1.r31, h1.r20, h1.r19]; exact hd₂₀
  have ci : CrIn s₁.gpr s₀.sp icb ct.length (s₁.gpr .r20) (s₁.gpr .r19).toNat s₂ :=
    ⟨he₂, h24, by rw [h25, BitVec.ofNat_toNat, BitVec.setWidth_eq], by rw [h26, h1.r23, hP],
      hd₂, by rw [h1.r28, hk₂.wr, h1.en.keeps.wr]; exact sc_X h, by rw [h1.r20, h1.r19, h1.r28]; exact sc_dx h⟩
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L X ci)) fun s₃ ⟨co, rd₃, wr₃, _⟩ => ?_)
  have hd₃ := hd₂.ok.of_eq rd₃ wr₃
  have f₂ : Frame [savedR (s₀.gpr .r9)] s₀.mem s₂.mem := by rw [hk₂.mem]; exact h1.en.frame
  have cf := co.frame
  rw [h1.r30, h1.r28, h1.r20, h1.r19] at cf
  have hH₃ : blockAt s₃.mem (s₁.gpr .r29 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .r3) := by
    rw [h1.r29, blockAt_frame cf (fun r hr => (ctx_crFrame' L₀ X₀ hd₂₀ r hr).sub_left (Lay.ctxSub (by decide))),
      ctxH_keep f₂ (ctx_saved L₀)]
  refine WP.seq (WP.mono (WP.with_rdwr (textAbsorb_ok L (a := a) (ct := ct) co.env hH₃ hd₃ (by rw [h1.r22]; exact ha)
    (by rw [h1.r23]; exact hP))) fun s₄ ⟨ta, rd₄, wr₄, _⟩ => ?_)
  have tf := ta.frame
  rw [h1.r30, h1.r31] at tf
  have sv₄ : SavedAt s₄.mem (s₀.gpr .r9) s₀ :=
    (((hk₂.mem ▸ h1.en.saved : SavedAt s₂.mem (s₀.gpr .r9) s₀)).frame cf (saved_crFrame L₀ X₀ hd₂₀)).frame tf
      (saved_taFrame L₀)
  have e31 : s₄.gpr .r31 = s₀.gpr .r9 := (ta.env.fr _ (by decide)).trans h1.r31
  refine WP.mono (restore_ok e31 (by have := ta.env.perm.w; rw [h1.r31] at this; exact Covers.right this) sv₄
    ta.env.sp (fun r hr => by rw [ta.env.fr r (by revert hr; revert r; decide)]; exact h1.en.low r hr))
    fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  have hc : ciphOf s₂.mem (s₁.gpr .r29) = ctxCiph s₀.mem (s₀.gpr .r3) := by
    rw [h1.r29]; exact ciph_keep f₂ (ctx_saved L₀)
  have ctr₂ : ∀ {P : Nat}, Ctr s₀.mem (s₀.gpr .r4 + BitVec.ofNat 64 48) (s₀.gpr .r4 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .r3)) icb P →
      Ctr s₂.mem (s₁.gpr .r30 + BitVec.ofNat 64 48) (s₁.gpr .r30 + BitVec.ofNat 64 64)
        (ciphOf s₂.mem (s₁.gpr .r29)) icb P := fun hc₀ => by
    rw [hc, h1.r30]
    exact hc₀.congr (blockAt_frame f₂ (stp_saved L₀ (by decide))) (blockAt_frame f₂ (stp_saved L₀ (by decide)))
  have dat₂ : bytesAt s₂.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat = bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat :=
    bytesAt_frame f₂ (data_saved hd₂₀.ok) (by have := hd₂₀.ok.lt; omega)
  have out₃ : Ctr s₀.mem (s₀.gpr .r4 + BitVec.ofNat 64 48) (s₀.gpr .r4 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .r3)) icb ct.length →
      bytesAt s₃.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat =
        xorKs (ctxCiph s₀.mem (s₀.gpr .r3)) icb ct.length (bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat) :=
    fun hc₀ => by
      have := co.out (ctr₂ hc₀)
      rw [hc, h1.r20, h1.r19, dat₂] at this
      exact this
  have hd₃₀ : DataOk (s₀.gpr .r4) (s₀.gpr .r9) s₃ (s₀.gpr .r7) (s₀.gpr .r8).toNat := hd₂₀.ok.of_eq rd₃ wr₃
  refine ⟨fun hc₀ => ?_, fun hc₀ => ?_, fun hc₀ hab => ?_, ?_⟩
  · rw [hm]
    have := co.ctr (ctr₂ hc₀)
    rw [hc, h1.r30, h1.r19] at this
    exact this.congr (blockAt_frame tf (stp_taFrame L₀ (.inr ⟨by decide, by decide⟩)))
      (blockAt_frame tf (stp_taFrame L₀ (.inr ⟨by decide, by decide⟩)))
  · rw [hm, bytesAt_frame tf (data_taFrame hd₃₀) (by have := hd₃₀.lt; omega)]
    exact out₃ hc₀
  · rw [hm]
    have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
    have hab₃ : Absorbed s₃.mem (s₀.gpr .r4 + BitVec.ofNat 64 16) (s₀.gpr .r4 + BitVec.ofNat 64 32)
        (ctxH s₀.mem (s₀.gpr .r3)) (ghashInput a ct) :=
      (hab.congr (blockAt_frame f₂ (stp_saved L₀ (by decide)))
        (bytesAt_frame f₂ (stp_saved L₀ (by omega)) (by omega))).congr
        (blockAt_frame cf (stp_crFrame X₀ hd₂₀ (by decide)))
        (bytesAt_frame cf (stp_crFrame X₀ hd₂₀ (by omega)) (by omega))
    have := ta.abs (by rw [h1.r30]; exact hab₃)
    rw [h1.r30, h1.r20, h1.r19, out₃ hc₀] at this
    exact this
  · rw [hm, blockAt_frame tf (by simpa using stp_taFrame L₀ (d := 0) (k := 16) (.inl (by decide))),
      blockAt_frame cf (by simpa using stp_crFrame X₀ hd₂₀ (d := 0) (k := 16) (by decide)),
      blockAt_frame f₂ (by simpa using stp_saved L₀ (d := 0) (k := 16) (by decide))]

theorem dec_run {s₀ : State} (h : streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (s₀.gpr .r5).toNat % 16) (hP : (s₀.gpr .r6).toNat = ct.length) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct true s' := by
  have L₀ := scLay h
  have X₀ := scX h
  refine WP.seq (WP.mono (sc1_wp (sc_W h)) fun s₁ h1 => ?_)
  have he₁ := sc_env h h1
  have L := L₀.v h1.r29 h1.r30 h1.r31
  have X : XOk (s₁.gpr .r29) (s₁.gpr .r30) (s₁.gpr .r31) (s₁.gpr .r28) := by rw [h1.r29, h1.r30, h1.r31, h1.r28]; exact X₀
  have f₁ : Frame [savedR (s₀.gpr .r9)] s₀.mem s₁.mem := h1.en.frame
  have hd₁₀ := sc_dataW h (s := s₁) h1.en.keeps.wr
  have hd₁ : DataOk (s₁.gpr .r30) (s₁.gpr .r31) s₁ (s₁.gpr .r20) (s₁.gpr .r19).toNat := by
    rw [h1.r30, h1.r31, h1.r20, h1.r19]; exact hd₁₀.ok
  have hH₁ : blockAt s₁.mem (s₁.gpr .r29 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .r3) := by
    rw [h1.r29]; exact ctxH_keep f₁ (ctx_saved L₀)
  refine WP.seq (WP.mono (WP.with_rdwr (textAbsorb_ok L (a := a) (ct := ct) he₁ hH₁ hd₁
    (by rw [h1.r22]; exact ha) (by rw [h1.r23]; exact hP))) fun s₄ ⟨ta, rd₄, wr₄, _⟩ => ?_)
  have tf := ta.frame
  rw [h1.r30, h1.r31] at tf
  refine WP.seq (WP.mono textArgs_ok fun s₅ ⟨h24, h25, h26, hg₅, hk₅⟩ => ?_)
  have he₅ : Env s₁.gpr s₀.sp s₅ := ta.env.keep (fun r hr => hg₅ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) hk₅.sp hk₅.rd hk₅.wr
  have hd₅₀ := sc_dataW h (s := s₅) (hk₅.wr.trans (wr₄.trans h1.en.keeps.wr))
  have hd₅ : DataW (s₁.gpr .r29) (s₁.gpr .r30) (s₁.gpr .r31) s₅ (s₁.gpr .r20) (s₁.gpr .r19).toNat := by
    rw [h1.r29, h1.r30, h1.r31, h1.r20, h1.r19]; exact hd₅₀
  have e20 := ta.env.fr .r20 (by decide)
  have e19 := ta.env.fr .r19 (by decide)
  have e23 := ta.env.fr .r23 (by decide)
  have ci : CrIn s₁.gpr s₀.sp icb ct.length (s₁.gpr .r20) (s₁.gpr .r19).toNat s₅ :=
    ⟨he₅, by rw [h24, e20], by rw [h25, e19, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by rw [h26, e23, h1.r23, hP], hd₅,
      by rw [h1.r28, hk₅.wr, wr₄, h1.en.keeps.wr]; exact sc_X h, by rw [h1.r20, h1.r19, h1.r28]; exact sc_dx h⟩
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L X ci)) fun s₆ ⟨co, rd₆, wr₆, _⟩ => ?_)
  have cf := co.frame
  rw [h1.r30, h1.r28, h1.r20, h1.r19] at cf
  have sv₆ : SavedAt s₆.mem (s₀.gpr .r9) s₀ :=
    ((h1.en.saved.frame tf (saved_taFrame L₀)) : SavedAt s₄.mem (s₀.gpr .r9) s₀) |>.frame
      (hk₅.mem ▸ cf) (saved_crFrame L₀ X₀ hd₅₀)
  have e31 : s₆.gpr .r31 = s₀.gpr .r9 := (co.env.fr _ (by decide)).trans h1.r31
  refine WP.mono (restore_ok e31 (by have := co.env.perm.w; rw [h1.r31] at this; exact Covers.right this) sv₆
    co.env.sp (fun r hr => by rw [co.env.fr r (by revert hr; revert r; decide)]; exact h1.en.low r hr))
    fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  have hc : ciphOf s₅.mem (s₁.gpr .r29) = ctxCiph s₀.mem (s₀.gpr .r3) := by
    rw [h1.r29, hk₅.mem, ciph_frame tf (ctx_taFrame L₀)]; exact ciph_keep f₁ (ctx_saved L₀)
  have blk₅ : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ 48 ≤ d ∧ d + 16 ≤ 80) →
      blockAt s₅.mem (s₀.gpr .r4 + BitVec.ofNat 64 d) = blockAt s₀.mem (s₀.gpr .r4 + BitVec.ofNat 64 d) :=
    fun hd => by
      rw [hk₅.mem, blockAt_frame tf (stp_taFrame L₀ hd), blockAt_frame f₁ (stp_saved L₀ (by omega))]
  have ctr₅ : ∀ {P : Nat}, Ctr s₀.mem (s₀.gpr .r4 + BitVec.ofNat 64 48) (s₀.gpr .r4 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .r3)) icb P →
      Ctr s₅.mem (s₁.gpr .r30 + BitVec.ofNat 64 48) (s₁.gpr .r30 + BitVec.ofNat 64 64)
        (ciphOf s₅.mem (s₁.gpr .r29)) icb P := fun hc₀ => by
    rw [hc, h1.r30]
    exact hc₀.congr (blk₅ (d := 48) (.inr ⟨by decide, by decide⟩)) (blk₅ (d := 64) (.inr ⟨by decide, by decide⟩))
  have dat₅ : bytesAt s₅.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat = bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat := by
    have hlt := hd₁₀.ok.lt
    rw [hk₅.mem, bytesAt_frame tf (data_taFrame hd₁₀.ok) (by omega), bytesAt_frame f₁ (data_saved hd₁₀.ok) (by omega)]
  have dat₁ : bytesAt s₁.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat = bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat :=
    bytesAt_frame f₁ (data_saved hd₁₀.ok) (by have := hd₁₀.ok.lt; omega)
  refine ⟨fun hc₀ => ?_, fun hc₀ => ?_, fun hc₀ hab => ?_, ?_⟩
  · rw [hm]
    have := co.ctr (ctr₅ hc₀)
    rw [hc, h1.r30, h1.r19] at this
    exact this
  · rw [hm]
    have := co.out (ctr₅ hc₀)
    rw [hc, h1.r20, h1.r19, dat₅] at this
    exact this
  · simp only [hm, ↓reduceIte]
    have hab₁ : Absorbed s₁.mem (s₀.gpr .r4 + BitVec.ofNat 64 16) (s₀.gpr .r4 + BitVec.ofNat 64 32)
        (ctxH s₀.mem (s₀.gpr .r3)) (ghashInput a ct) :=
      hab.congr (blockAt_frame f₁ (stp_saved L₀ (by decide)))
        (bytesAt_frame f₁ (stp_saved L₀ (by omega)) (by omega))
    have := ta.abs (by rw [h1.r30]; exact hab₁)
    rw [h1.r30, h1.r20, h1.r19, dat₁] at this
    rw [← hk₅.mem] at this
    exact this.congr (blockAt_frame cf (stp_crFrame X₀ hd₅₀ (by decide)))
      (bytesAt_frame cf (stp_crFrame X₀ hd₅₀ (by omega)) (by omega))
  · rw [hm, blockAt_frame cf (by simpa using stp_crFrame X₀ hd₅₀ (d := 0) (k := 16) (by decide))]
    simpa using blk₅ (d := 0) (.inl (by decide))

theorem streamEncrypt_wp {s₀ : State} (h : streamEncryptPPC64LE.pre s₀) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamEncryptPPC64LE.post s₀ s' := by
  have h' : streamCryptPre s₀ := h
  have h₀ := enc_run h' 0 (a := List.replicate ((s₀.gpr .r5).toNat % 16) 0)
    (ct := List.replicate (s₀.gpr .r6).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      let ciph := ctxCiph s₀.mem (s₀.gpr .r3)
      let hh := ctxH s₀.mem (s₀.gpr .r3)
      StreamRepr s₀.mem (s₀.gpr .r4) ciph hh i.1 i.2.1 (gctr ciph (inc32 (j0 hh i.1)) i.2.2) ∧
        s₀.gpr .r5 = BitVec.ofNat 64 i.2.1.length ∧ (s₀.gpr .r6).toNat = i.2.2.length)
    fun i hi => enc_run h' (inc32 (j0 (ctxH s₀.mem (s₀.gpr .r3)) i.1)) (a := i.2.1)
      (ct := gctr (ctxCiph s₀.mem (s₀.gpr .r3)) (inc32 (j0 (ctxH s₀.mem (s₀.gpr .r3)) i.1)) i.2.2)
      (by rw [hi.2.1, toNat_mod16]) (by rw [Proof.Gcm.length_gctr]; exact hi.2.2))
    fun s' hh => ⟨hh.1, fun iv a p hs hl hp => ?_⟩
  obtain ⟨-, eo⟩ := hh.2 ⟨iv, a, p⟩ ⟨hs, hl, hp⟩
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, hct⟩ := hs
  have hl' : (gctr (ctxCiph s₀.mem (s₀.gpr .r3))
      (inc32 (j0 (ctxH s₀.mem (s₀.gpr .r3)) iv)) p).length = p.length := Proof.Gcm.length_gctr _ _ _
  have eo₁ := eo.ctr hct
  have eo₂ := eo.out hct
  have eo₃ := eo.abs hct hab
  simp only [Bool.false_eq_true, ite_false] at eo₃
  rw [hl'] at eo₁ eo₂ eo₃
  rw [← Proof.Gcm.gctr_append] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [Proof.Gcm.length_gctr, List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' hl']

theorem streamDecrypt_wp {s₀ : State} (h : streamDecryptPPC64LE.pre s₀) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamDecryptPPC64LE.post s₀ s' := by
  have h' : streamCryptPre s₀ := h
  have h₀ := dec_run h' 0 (a := List.replicate ((s₀.gpr .r5).toNat % 16) 0)
    (ct := List.replicate (s₀.gpr .r6).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      let ciph := ctxCiph s₀.mem (s₀.gpr .r3)
      let hh := ctxH s₀.mem (s₀.gpr .r3)
      StreamRepr s₀.mem (s₀.gpr .r4) ciph hh i.1 i.2.1 i.2.2 ∧
        s₀.gpr .r5 = BitVec.ofNat 64 i.2.1.length ∧ (s₀.gpr .r6).toNat = i.2.2.length)
    fun i hi => dec_run h' (inc32 (j0 (ctxH s₀.mem (s₀.gpr .r3)) i.1)) (a := i.2.1) (ct := i.2.2)
      (by rw [hi.2.1, toNat_mod16]) hi.2.2)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => ?_⟩
  obtain ⟨-, eo⟩ := hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, hct⟩ := hs
  have eo₁ := eo.ctr hct
  have eo₂ := eo.out hct
  have eo₃ := eo.abs hct hab
  simp only [ite_true] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]

end VG.Proof.Sm4Gcm.PPC64LE
