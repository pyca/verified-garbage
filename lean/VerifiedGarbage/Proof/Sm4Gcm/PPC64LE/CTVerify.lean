module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTFin
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTVerify
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTFin
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTVerify
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt
public import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
meta import VerifiedGarbage.Spec.Gcm
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt

/-! ### `Sm4Gcm.PPC64LE.StreamVerify`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_stream_verify`

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/StreamVerify.lean`), with SM4's tag: the entry saves our caller's
registers and keeps the arguments in `r19`–`r30` (`ver1_wp`); a tag length
`tagLenOk` rejects returns 0; otherwise `recv` pads the received tag, `finTag 0`
puts the tag into `W` and `cmp 0` compares its first bytes with the
received ones (`ver_run`, `streamVerify_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov recv cmp tagLenOk)
open VG.Proof.AesGcm.PPC64LE (Env Lay Perm Keeps Entered SavedAt savedR save_ok restore_ok covers_mem
  covers_prefix covers_off bytesAt_frame blockAt_frame ctxH_keep saved_w toNat_mod16 WP.forall_det
  WP.with_rdwr Lay.saved_st bytesAt_take tagLenOk_bounds tagLenOk_ok recv_ok cmp_ok eval_zero)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ghashInput fullTag zeros)
open VG.Spec.Sm4.Gcm (ctxCiph)

section
variable {s₀ : State} (h : verPre s₀)
include h

theorem verLay : Lay (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r9) := by
  obtain ⟨-, -, dcs, dcw, -, dsw, -, fc, fs, -, fw, -⟩ := h
  have fw' : (s₀.gpr .r9).toNat + 2560 ≤ 2 ^ 64 := fw
  exact Lay.of fc fs (by omega_using [fw']) dcs (dcw.sub_right (Region.sub_prefix (by decide)))
    (dsw.sub_right (Region.sub_prefix (by decide)))

theorem verX : XOk (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r9) (s₀.gpr .r10) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, dcx, dsx, -, dwx, fx⟩ := h
  exact ⟨fx, dcx, dsx, dwx⟩

theorem ver_W' : Covers [⟨s₀.gpr .r9, scrBytes⟩] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

theorem ver_W : Covers [⟨s₀.gpr .r9, 2560⟩] s₀.wr := covers_prefix (ver_W' h) (by decide)

theorem ver_X : Covers [xR (s₀.gpr .r10)] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

end

/-- After the entry of `verify`, from `s₀`. -/
structure SV1 (s₀ s₁ : State) : Prop where
  en : Entered s₀ (s₀.gpr .r9) s₁
  r31 : s₁.gpr .r31 = s₀.gpr .r9
  r30 : s₁.gpr .r30 = s₀.gpr .r4
  r29 : s₁.gpr .r29 = s₀.gpr .r3
  r22 : s₁.gpr .r22 = s₀.gpr .r5
  r23 : s₁.gpr .r23 = s₀.gpr .r6
  r20 : s₁.gpr .r20 = s₀.gpr .r7
  r19 : s₁.gpr .r19 = s₀.gpr .r8
  r28 : s₁.gpr .r28 = s₀.gpr .r10

theorem ver1_wp {s₀ : State} (hW : Covers [⟨s₀.gpr .r9, 2560⟩] s₀.wr) :
    WP isa (.block verEntry) s₀ (SV1 s₀) := by
  refine WP.block_append (WP.mono (save_ok (b := .r9) (by decide) hW) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  obtain e3 : s₁.gpr .r3 = s₀.gpr .r3 := hg _ (by decide) (by decide)
  obtain e4 : s₁.gpr .r4 = s₀.gpr .r4 := hg _ (by decide) (by decide)
  obtain e5 : s₁.gpr .r5 = s₀.gpr .r5 := hg _ (by decide) (by decide)
  obtain e6 : s₁.gpr .r6 = s₀.gpr .r6 := hg _ (by decide) (by decide)
  obtain e7 : s₁.gpr .r7 = s₀.gpr .r7 := hg _ (by decide) (by decide)
  obtain e8 : s₁.gpr .r8 = s₀.gpr .r8 := hg _ (by decide) (by decide)
  obtain e10 : s₁.gpr .r10 = s₀.gpr .r10 := hg _ (by decide) (by decide)
  crun [mov, BitVec.or_self, e3, e4, e5, e6, e7, e8, e10, h31]
  refine ⟨⟨fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hg],
    ⟨hk.rd, hk.wr, hk.sp, hk.lr⟩, hsv, hf⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [h31]

/-- The environment after the entry. -/
theorem ver_env {s₀ s₁ : State} (h : verPre s₀) (h1 : SV1 s₀ s₁) : Env s₁.gpr s₀.sp s₁ := by
  obtain ⟨hrd, hwr, -⟩ := h
  obtain perm : Perm (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r9) s₁ :=
    (⟨covers_mem (by rw [hrd]; simp), covers_mem (by rw [hwr]; simp),
      covers_prefix (covers_mem (r := ⟨s₀.gpr .r9, scrBytes⟩) (by rw [hwr]; simp)) (by decide)⟩ :
      Perm (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r9) s₀).of_eq h1.en.keeps.rd h1.en.keeps.wr
  exact ⟨fun _ _ => rfl, h1.en.keeps.sp, by rw [h1.r29, h1.r30, h1.r31]; exact perm⟩

/-- What `verify` promises, for the additional data `a` and the text `ct`. -/
def VerPost (s₀ : State) (a ct : List Byte) (s : State) : Prop :=
  ∀ iv, StreamRepr s₀.mem (s₀.gpr .r4) (ctxCiph s₀.mem (s₀.gpr .r3))
      (ctxH s₀.mem (s₀.gpr .r3)) iv a ct → s₀.gpr .r5 = BitVec.ofNat 64 a.length →
    let t := fullTag (ctxCiph s₀.mem (s₀.gpr .r3)) (ctxH s₀.mem (s₀.gpr .r3)) iv a ct
    if Spec.Gcm.tagLenOk (s₀.gpr .r8).toNat ∧ t.take (s₀.gpr .r8).toNat = bytesAt s₀.mem (s₀.gpr .r7)
        (s₀.gpr .r8).toNat then s.gpr .r3 = 1
    else s.gpr .r3 = 0

theorem ver_run [VG.Proof.Gcm.PPC64LE.GhashLaw] {s₀ : State} (h : verPre s₀) {a ct : List Byte} (ha : a.length % 16 = (s₀.gpr .r5).toNat % 16)
    (hP : (s₀.gpr .r6).toNat = ct.length) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ VerPost s₀ a ct s' := by
  obtain L₀ := verLay h
  obtain X₀ := verX h
  have hh := h
  obtain ⟨hrd, -, -, -, -, dsw, dtw, -, -, -, -, -⟩ := hh
  obtain hTr : Covers [⟨s₀.gpr .r7, (s₀.gpr .r8).toNat⟩] (s₀.rd ++ s₀.wr) :=
    covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain dT : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨s₀.gpr .r7, (s₀.gpr .r8).toNat⟩ : Region).Disjoint
      ⟨s₀.gpr .r9 + BitVec.ofNat 64 d, k⟩ := fun hd => dtw.sub_right (VG.Offset.sub_base _ (by simp only [scrBytes]; omega_using [hd]))
  refine WP.seq (WP.mono (ver1_wp (ver_W h)) fun s₁ h1 => ?_)
  obtain he₁ := ver_env h h1
  obtain L := L₀.v h1.r29 h1.r30 h1.r31
  obtain tl19 : s₁.gpr .r19 = BitVec.ofNat 64 (s₀.gpr .r8).toNat := by
    rw [h1.r19, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (tagLenOk_ok tl19 (s₀.gpr .r8).isLt) fun s₃ ⟨h25, g₃, k₃⟩ => ?_)
  obtain he₃ := he₁.keep (fun r hr => g₃ r (by revert r; decide) (by revert r; decide)) k₃.sp k₃.rd k₃.wr
  obtain sv₃ : SavedAt s₃.mem (s₀.gpr .r9) s₀ := k₃.mem ▸ h1.en.saved
  obtain mid : WP isa (.ite (.zero .d .r25) (.block [.li .r3 0]) (.seq recv (.seq (finTag 0) (cmp 0)))) s₃
      fun s' => Env s₁.gpr s₀.sp s' ∧ SavedAt s'.mem (s₀.gpr .r9) s₀ ∧ VerPost s₀ a ct s' := by
    refine WP.ite _ (eval_zero h25 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hbad : Spec.Gcm.tagLenOk (s₀.gpr .r8).toNat = false := by
        cases e : Spec.Gcm.tagLenOk (s₀.gpr .r8).toNat
        · rfl
        · simp [e] at ht
      obtain h₀ : WP isa (.block [.li .r3 0]) s₃ fun s' => s'.gpr .r3 = 0 ∧
          (∀ r, r ≠ .r3 → s'.gpr r = s₃.gpr r) ∧ Keeps s₃ s' := by
        crun []
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      refine WP.mono h₀ fun s' ⟨z3, g, k⟩ => ⟨he₃.keep (fun r hr => g r (by revert r; decide)) k.sp k.rd k.wr,
        k.mem ▸ sv₃, fun iv _ _ => ?_⟩
      simp only [hbad, Bool.false_eq_true, false_and, ite_false]
      exact z3
    obtain hok : Spec.Gcm.tagLenOk (s₀.gpr .r8).toNat = true := by
      cases e : Spec.Gcm.tagLenOk (s₀.gpr .r8).toNat
      · simp [e] at hf
      · rfl
    obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
    obtain hTr₃ : Covers [⟨s₁.gpr .r20, (s₀.gpr .r8).toNat⟩] (s₃.rd ++ s₃.wr) := by
      rw [k₃.rd, k₃.wr, h1.en.keeps.rd, h1.en.keeps.wr, h1.r20]; exact hTr
    obtain hTd : (⟨s₁.gpr .r20, (s₀.gpr .r8).toNat⟩ : Region).Disjoint ⟨s₁.gpr .r31 + BitVec.ofNat 64 256, 16⟩ := by
      rw [h1.r20, h1.r31]; exact dT (by decide)
    refine WP.seq (WP.mono (recv_ok he₃ tl19 t1 t16 hTr₃ hTd) fun s₄ ⟨hb₄, hf₄, g₄, k₄⟩ => ?_)
    obtain he₄ := he₃.keep (fun r hr => g₄ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) k₄.sp k₄.rd k₄.wr
    rw [h1.r31] at hf₄ hb₄
    obtain f₀₄ : Frame [savedR (s₀.gpr .r9), ⟨s₀.gpr .r9 + BitVec.ofNat 64 256, 16⟩] s₀.mem s₄.mem :=
      (h1.en.frame.mono (by simp)).trans ((k₃.mem ▸ hf₄ : Frame _ s₁.mem s₄.mem).mono (by simp))
    obtain dc₀₄ : ∀ r ∈ [savedR (s₀.gpr .r9), ⟨s₀.gpr .r9 + BitVec.ofNat 64 256, 16⟩],
        (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L₀.cw'.sub_right (Lay.wSub (by decide))
      · exact L₀.cw'.sub_right (Lay.wSub (by decide))
    obtain ds₀₄ : ∀ r ∈ [savedR (s₀.gpr .r9), ⟨s₀.gpr .r9 + BitVec.ofNat 64 256, 16⟩],
        (⟨s₀.gpr .r4, 80⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa using (L₀.saved_st (d := 0) (k := 80) (by decide)).symm
      · exact dsw.sub_right (VG.Offset.sub_base _ (by decide))
    obtain hH₄ : blockAt s₄.mem (s₁.gpr .r29 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .r3) := by
      rw [h1.r29]; exact ctxH_keep f₀₄ dc₀₄
    obtain X : XOk (s₁.gpr .r29) (s₁.gpr .r30) (s₁.gpr .r31) (s₁.gpr .r28) := by rw [h1.r29, h1.r30, h1.r31, h1.r28]; exact X₀
    refine WP.seq (WP.mono (WP.with_rdwr (finTag_ok L X (o := 0) (.inl rfl) (a := a) (ct := ct) he₄
      (by rw [h1.r28, k₄.wr, k₃.wr, h1.en.keeps.wr]; exact ver_X h) hH₄ (by rw [h1.r22]; exact ha)
      (by rw [h1.r23]; exact hP))) fun s₅ ⟨fo, rd₅, wr₅, _⟩ => ?_)
    refine WP.mono (cmp_ok fo.env (o := 0) (.inl rfl) tl19 t1 t16) fun s₇ ⟨h3₇, hf₇, g₇, k₇⟩ => ?_
    have fof := fo.frame
    rw [h1.r30, h1.r31, h1.r28] at fof
    refine ⟨fo.env.keep (fun r hr => g₇ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) k₇.sp k₇.rd k₇.wr, ?_, fun iv hs hl => ?_⟩
    · have sv₅ := (sv₃.frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))).frame fof
        (saved_tagFrame L₀ X₀ (.inl rfl))
      rw [h1.r31] at hf₇
      exact sv₅.frame hf₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))
    · have ht' : bytesAt s₅.mem (s₁.gpr .r31 + BitVec.ofNat 64 0) 16 =
          fullTag (ctxCiph s₀.mem (s₀.gpr .r3)) (ctxH s₀.mem (s₀.gpr .r3)) iv a ct :=
        fin_out f₀₄ dc₀₄ ds₀₄ h1.r29 h1.r30 h1.r22 fo hs hl
      obtain hrc : bytesAt s₅.mem (s₁.gpr .r31 + BitVec.ofNat 64 256) 16 =
          bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat ++ zeros (16 - (s₀.gpr .r8).toNat) := by
        rw [h1.r31, bytesAt_frame fof (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl
            · exact ((dsw.sub_right (VG.Offset.sub_base (d := 256) (n := 16) _ (by decide))).sub_left
                (Region.sub_prefix (by decide))).symm
            · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
            · simpa using Lay.w_w (w := s₀.gpr .r9) (a := 256) (n := 16) (d := 0) (k := 16) (.inr (by decide))
                (by decide) (by decide)
            · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
            · exact X₀.wx.sub_left (Lay.wSub (by decide))) (by decide), hb₄, k₃.mem,
          ← h1.r20, bytesAt_frame h1.en.frame (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [h1.r20]
            exact dT (d := 128) (k := 120) (by decide)) (by omega_using []), h1.r20]
      obtain hX : (bytesAt s₅.mem (s₁.gpr .r31 + BitVec.ofNat 64 0) (s₀.gpr .r8).toNat ++
            zeros (16 - (s₀.gpr .r8).toNat) = bytesAt s₅.mem (s₁.gpr .r31 + BitVec.ofNat 64 256) 16) ↔
          (fullTag (ctxCiph s₀.mem (s₀.gpr .r3)) (ctxH s₀.mem (s₀.gpr .r3)) iv a ct).take
            (s₀.gpr .r8).toNat = bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat := by
        rw [bytesAt_take _ _ t16, ht', hrc, List.append_cancel_right_eq]
      simp only [hok, true_and]
      by_cases e : (fullTag (ctxCiph s₀.mem (s₀.gpr .r3)) (ctxH s₀.mem (s₀.gpr .r3)) iv a ct).take
          (s₀.gpr .r8).toNat = bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat
      · simp only [e, ite_true]
        rw [h3₇]; simp only [hX.mpr e, ite_true]
      · simp only [e, ite_false]
        rw [h3₇]; simp only [show ¬ _ from fun x => e (hX.mp x), ite_false]
  refine WP.seq (WP.mono mid fun s₄ ⟨he, sv, vp⟩ => ?_)
  obtain e31 : s₄.gpr .r31 = s₀.gpr .r9 := (he.fr _ (by decide)).trans h1.r31
  refine WP.mono (restore_ok e31 (by have := he.perm.w; rw [h1.r31] at this; exact Covers.right this) sv
    he.sp (fun r hr => by rw [he.fr r (by revert hr; revert r; decide)]; exact h1.en.low r hr))
    fun s' ⟨ga, _, h3, _⟩ => ⟨ga, fun iv hs hl => ?_⟩
  have := vp iv hs hl
  rw [h3]; exact this

theorem streamVerify_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {s₀ : State} (h : streamVerifyPPC64LE.pre s₀) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ streamVerifyPPC64LE.post s₀ s' := by
  have h' : verPre s₀ := h
  obtain h₀ := ver_run h' (a := List.replicate ((s₀.gpr .r5).toNat % 16) 0)
    (ct := List.replicate (s₀.gpr .r6).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte =>
      s₀.gpr .r5 = BitVec.ofNat 64 i.1.length ∧ (s₀.gpr .r6).toNat = i.2.length)
    fun i hi => WP.mono (ver_run h' (a := i.1) (ct := i.2) (by rw [hi.1, toNat_mod16]) hi.2) fun _ hh => hh.2)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => by
      have := hh.2 ⟨a, c⟩ ⟨hl, hp⟩ iv hs hl
      simp only at this ⊢
      split <;> simp_all⟩

end VG.Proof.Sm4Gcm.PPC64LE

end

end

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_stream_verify` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/CTVerify.lean`): the invariant fixes what `finish`'s
does (`FinI`), and the received tag's address and length (`r20`, `r19`);
the branch on the tag length is on that public length, and the comparison
does not branch.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (recv cmp tagLenOk)
open VG.Proof.AesGcm.PPC64LE (CT ct_of CT.taintEq Env Lay Keeps covers_mem eval_zero recv_ok cmp_ok
  tagLenOk_ok tagLenOk_bounds tagLenOk_taint recv_taint cmp_taint li3_taint WP.with_rdwr)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- In `verify`, after the entry: the received tag's `tl` bytes at `Tp`,
apart from `W`, which the state may read. -/
def VerI (c st w x sp : Addr) (A T Tp : BitVec 64) (tl : Nat) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧ V .r22 = A ∧
    V .r23 = T ∧ V .r20 = Tp ∧ V .r19 = BitVec.ofNat 64 tl ∧ Env V sp s ∧ Covers [⟨Tp, tl⟩] (s.rd ++ s.wr) ∧
    (⟨Tp, tl⟩ : Region).Disjoint ⟨w, 2560⟩ ∧ Covers [xR x] s.wr

theorem verEntry_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]) (.block verEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {c st w x sp : Addr} (L : Lay c st w) (X : XOk c st w x) {A T Tp : BitVec 64}
  {tl : Nat}
include L X

/-- `verify` after the tag length is known to be allowed. -/
theorem verOk_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] (t1 : 1 ≤ tl) (t16 : tl ≤ 16) :
    CT (VerI c st w x sp A T Tp tl) (.seq recv (.seq (finTag 0) (cmp 0))) := by
  refine CT.seq (J := VerI c st w x sp A T Tp tl) ?_ (fun s ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd, hx⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := recv_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, i₁, j₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, i₂, j₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.r31, h₂.r31, d₁, d₂]
  · refine WP.mono (recv_ok he j t1 t16 (by rw [i]; exact hT) (by rw [i, d]; exact hTd.sub_right (Lay.wSub
      (by decide)))) fun s' ⟨_, _, hg, hk⟩ => ⟨V, a, b, d, e, f, g, i, j, he.keep (fun r hr => hg r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) hk.sp hk.rd hk.wr, by rw [hk.rd, hk.wr]; exact hT, hTd, by rw [hk.wr]; exact hx⟩
  refine CT.seq (J := VerI c st w x sp A T Tp tl)
    ((finTag_ct L X (o := 0) (.inl rfl)).mono fun s ⟨V, a, b, d, e, f, g, _, _, he, _, _, hx⟩ =>
      ⟨V, a, b, d, e, f, g, he, hx⟩)
    (fun s ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd, hx⟩ => WP.mono (WP.with_rdwr (finTag_ok (L.v a b d)
      (by rw [a, b, d, e]; exact X) (o := 0)
      (.inl rfl) (a := List.replicate (A.toNat % 16) 0) (ct := List.replicate T.toNat 0) he (by rw [e]; exact hx) rfl
      (by simp [f]) (by simp [g]))) fun s' ⟨fo, rd, wr, _⟩ =>
        ⟨V, a, b, d, e, f, g, i, j, fo.env, by rw [rd, wr]; exact hT, hTd, by rw [wr]; exact hx⟩) ?_
  obtain ⟨_, hc⟩ := cmp_taint
  refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, _, j₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, _, j₂, h₂, _⟩ =>
    ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
  · rw [h₁.r31, h₂.r31, d₁, d₂]

/-- The same, for correctness: `W` is kept in `r31`. -/
theorem verOk_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] (t1 : 1 ≤ tl) (t16 : tl ≤ 16) {s : State} (h : VerI c st w x sp A T Tp tl s) :
    WP isa (.seq recv (.seq (finTag 0) (cmp 0))) s fun s' => s'.gpr .r31 = w ∧ s'.sp = sp := by
  obtain ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd, hx⟩ := h
  refine WP.seq (WP.mono (recv_ok he j t1 t16 (by rw [i]; exact hT) (by rw [i, d]; exact hTd.sub_right (Lay.wSub
    (by decide)))) fun s₁ ⟨_, _, hg, hk⟩ => ?_)
  have he₁ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr
  refine WP.seq (WP.mono (finTag_ok (L.v a b d) (by rw [a, b, d, e]; exact X) (o := 0) (.inl rfl)
    (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he₁ (by rw [e, hk.wr]; exact hx) rfl (by simp [f]) (by simp [g])) fun s₂ fo => ?_)
  refine WP.mono (cmp_ok fo.env (o := 0) (.inl rfl) j t1 t16) fun s' ⟨_, _, hg', hk'⟩ =>
    ⟨by rw [hg' _ (by decide) (by decide) (by decide) (by decide) (by decide), fo.env.r31, d],
      by rw [hk'.sp, fo.env.sp]⟩

end

theorem streamVerify_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] : ConstantTime isa streamVerifyPPC64LE.pre streamVerifyPPC64LE.pub streamVerify := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp⟩ := hq
  have h₁' : verPre σ₁ := h₁
  have L := verLay h₁'
  have X := verX h₁'
  let I₀ : State → Prop := fun s => verPre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧ s.gpr .r4 = σ₁.gpr .r4 ∧
    s.gpr .r5 = σ₁.gpr .r5 ∧ s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧ s.gpr .r8 = σ₁.gpr .r8 ∧
    s.gpr .r9 = σ₁.gpr .r9 ∧ s.gpr .r10 = σ₁.gpr .r10 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, q9.symm, q10.symm, qsp.symm⟩, ?_⟩
  let tl := (σ₁.gpr .r8).toNat
  let VI := VerI (σ₁.gpr .r3) (σ₁.gpr .r4) (σ₁.gpr .r9) (σ₁.gpr .r10) σ₁.sp (σ₁.gpr .r5) (σ₁.gpr .r6)
    (σ₁.gpr .r7) tl
  refine CT.seq (J := VI) ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := verEntry_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9, e10]⟩) hc
  · refine WP.mono (ver1_wp (ver_W hs)) fun s₁ h1 => ?_
    have hT : Covers [⟨s.gpr .r7, (s.gpr .r8).toNat⟩] (s₁.rd ++ s₁.wr) := by
      rw [h1.en.keeps.rd, h1.en.keeps.wr, hs.1]; exact covers_mem (List.mem_append_left _ (by simp))
    have hTd : (⟨s.gpr .r7, (s.gpr .r8).toNat⟩ : Region).Disjoint ⟨s.gpr .r9, 2560⟩ :=
      hs.2.2.2.2.2.2.1.sub_right (Region.sub_prefix (by decide))
    refine ⟨s₁.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h1.r29, e3]
    · rw [h1.r30, e4]
    · rw [h1.r31, e9]
    · rw [h1.r28, e10]
    · rw [h1.r22, e5]
    · rw [h1.r23, e6]
    · rw [h1.r20, e7]
    · rw [h1.r19, e8, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [← esp]; exact ver_env hs h1
    · simp only [tl]; rw [← e7, ← e8]; exact hT
    · simp only [tl]; rw [← e7, ← e8, ← e9]; exact hTd
    · rw [← e10, h1.en.keeps.wr]; exact ver_X hs
  -- the tag length
  let ok := Spec.Gcm.tagLenOk tl
  let J : State → Prop := fun s => VI s ∧ s.gpr .r25 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd, hx⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, _, j₁, h₁, _⟩ ⟨_, _, _, _, _, _, _, _, j₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
  · refine WP.mono (tagLenOk_ok (by rw [he.fr _ (by decide), j]) (σ₁.gpr .r8).isLt) fun s' ⟨h25, hg, hk⟩ =>
      ⟨⟨V, a, b, d, e, f, g, i, j, he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide))
        hk.sp hk.rd hk.wr, by rw [hk.rd, hk.wr]; exact hT, hTd, by rw [hk.wr]; exact hx⟩, h25⟩
  have ev : ∀ s, J s → isa.eval (.zero .d .r25) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s h => eval_zero h.2 (by split <;> decide)
  refine CT.seq (J := fun s => s.gpr .r31 = σ₁.gpr .r9 ∧ s.sp = σ₁.sp) ?_ (fun s hs => ?_) ?_
  · refine CT.ite _ ev (fun hb => ?_) (fun hb => ?_)
    · obtain ⟨_, hc⟩ := li3_taint
      exact CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, _, _, _, _, _, _, h₁, _⟩, _⟩ ⟨⟨_, _, _, _, _, _, _, _, _, h₂, _⟩, _⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => by simp at hr⟩) hc
    · have hok : ok = true := by cases e : ok <;> simp_all
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      exact (verOk_ct L X t1 t16).mono fun s h => h.1
  · refine WP.ite _ (ev s hs) (fun hb => ?_) (fun hb => ?_)
    · obtain ⟨⟨V, _, _, d, _, _, _, _, _, he, _⟩, _⟩ := hs
      have h₀ : WP isa (.block [.li .r3 0]) s fun s' => (∀ r, r ≠ .r3 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
        crun []
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₀ fun s' ⟨hg, hk⟩ => ⟨by rw [hg _ (by decide), he.r31, d], by rw [hk.sp, he.sp]⟩
    · have hok : ok = true := by cases e : ok <;> simp_all
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      exact verOk_wp L X t1 t16 hs.1
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .r9) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.Sm4Gcm.PPC64LE
