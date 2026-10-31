module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
import VerifiedGarbage.Proof.AesGcm.PPC64LE.FinTag
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Impl.AesGcm.PPC64LE

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_stream_verify`

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/StreamVerify.lean`): the entry saves our caller's
registers and keeps the arguments in `r19`–`r30` (`ver1_wp`); a tag length
`tagLenOk` rejects returns 0; otherwise `recv` pads the received tag, `finTag 0`
puts the tag into `W` and `cmp 0` compares its first bytes with the
received ones (`ver_run`, `streamVerify_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput fullTag zeros)

theorem bytesAt_take (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) : bytesAt m p k = (bytesAt m p n).take k := by
  rw [show n = k + (n - k) by omega, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]

theorem tagLenOk_bounds {tl : Nat} (h : Spec.Gcm.tagLenOk tl = true) : 1 ≤ tl ∧ tl ≤ 16 := by
  simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

section
variable {s₀ : State} (h : verPre s₀)
include h

theorem verLay : Lay (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r10) := by
  obtain ⟨-, -, dcs, dcw, -, dsw, -, fc, fs, -, fw, -⟩ := h
  exact Lay.of fc fs fw dcs dcw dsw

theorem ver_W : Covers [⟨s₀.gpr .r10, 2560⟩] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

end

/-- After the entry of `verify`, from `s₀`. -/
structure SV1 (s₀ s₁ : State) : Prop where
  en : Entered s₀ (s₀.gpr .r10) s₁
  r31 : s₁.gpr .r31 = s₀.gpr .r10
  r30 : s₁.gpr .r30 = s₀.gpr .r5
  r29 : s₁.gpr .r29 = s₀.gpr .r3
  r28 : s₁.gpr .r28 = s₀.gpr .r4
  r22 : s₁.gpr .r22 = s₀.gpr .r6
  r23 : s₁.gpr .r23 = s₀.gpr .r7
  r20 : s₁.gpr .r20 = s₀.gpr .r8
  r19 : s₁.gpr .r19 = s₀.gpr .r9

theorem ver1_wp {s₀ : State} (hW : Covers [⟨s₀.gpr .r10, 2560⟩] s₀.wr) :
    WP isa (.block verEntry) s₀ (SV1 s₀) := by
  refine WP.block_append (WP.mono (save_ok (b := .r10) (by decide) hW) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e3 : s₁.gpr .r3 = s₀.gpr .r3 := hg _ (by decide) (by decide)
  have e4 : s₁.gpr .r4 = s₀.gpr .r4 := hg _ (by decide) (by decide)
  have e5 : s₁.gpr .r5 = s₀.gpr .r5 := hg _ (by decide) (by decide)
  have e6 : s₁.gpr .r6 = s₀.gpr .r6 := hg _ (by decide) (by decide)
  have e7 : s₁.gpr .r7 = s₀.gpr .r7 := hg _ (by decide) (by decide)
  have e8 : s₁.gpr .r8 = s₀.gpr .r8 := hg _ (by decide) (by decide)
  have e9 : s₁.gpr .r9 = s₀.gpr .r9 := hg _ (by decide) (by decide)
  crun [mov, BitVec.or_self, e3, e4, e5, e6, e7, e8, e9, h31]
  refine ⟨⟨fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hg],
    ⟨hk.rd, hk.wr, hk.sp, hk.lr⟩, hsv, hf⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [h31]

/-- The environment after the entry. -/
theorem ver_env {s₀ s₁ : State} (h : verPre s₀) (h1 : SV1 s₀ s₁) : Env s₁.gpr s₀.sp s₁ := by
  obtain ⟨hrd, hwr, -⟩ := h
  have perm : Perm (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r10) s₁ :=
    (⟨covers_mem (by rw [hrd]; simp), covers_mem (by rw [hwr]; simp), covers_mem (by rw [hwr]; simp)⟩ :
      Perm (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r10) s₀).of_eq h1.en.keeps.rd h1.en.keeps.wr
  exact ⟨fun _ _ => rfl, h1.en.keeps.sp, by rw [h1.r29, h1.r30, h1.r31]; exact perm⟩

/-- What `verify` promises, for the additional data `a` and the text `ct`. -/
def VerPost (s₀ : State) (a ct : List Byte) (s : State) : Prop :=
  ∀ iv, StreamRepr s₀.mem (s₀.gpr .r5) (ctxCiph s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat)
      (ctxH s₀.mem (s₀.gpr .r3)) iv a ct → s₀.gpr .r6 = BitVec.ofNat 64 a.length →
    let t := fullTag (ctxCiph s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat) (ctxH s₀.mem (s₀.gpr .r3)) iv a ct
    if Spec.Gcm.tagLenOk (s₀.gpr .r9).toNat ∧ t.take (s₀.gpr .r9).toNat = bytesAt s₀.mem (s₀.gpr .r8)
        (s₀.gpr .r9).toNat then s.gpr .r3 = 1
    else s.gpr .r3 = 0

theorem ver_run [VG.Proof.Gcm.PPC64LE.GhashLaw] {s₀ : State} (h : verPre s₀) {a ct : List Byte} (ha : a.length % 16 = (s₀.gpr .r6).toNat % 16)
    (hP : (s₀.gpr .r7).toNat = ct.length) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ VerPost s₀ a ct s' := by
  have L₀ := verLay h
  have hR : (s₀.gpr .r4).toNat = 10 ∨ (s₀.gpr .r4).toNat = 12 ∨ (s₀.gpr .r4).toNat = 14 :=
    h.2.2.2.2.2.2.2.2.2.2.2
  have hh := h
  obtain ⟨hrd, -, -, -, -, dsw, dtw, -, -, -, -, -⟩ := hh
  have hTr : Covers [⟨s₀.gpr .r8, (s₀.gpr .r9).toNat⟩] (s₀.rd ++ s₀.wr) :=
    covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have dT : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨s₀.gpr .r8, (s₀.gpr .r9).toNat⟩ : Region).Disjoint
      ⟨s₀.gpr .r10 + BitVec.ofNat 64 d, k⟩ := fun hd => dtw.sub_right (Lay.wSub hd)
  refine WP.seq (WP.mono (ver1_wp (ver_W h)) fun s₁ h1 => ?_)
  have he₁ := ver_env h h1
  have L := L₀.v h1.r29 h1.r30 h1.r31
  have tl19 : s₁.gpr .r19 = BitVec.ofNat 64 (s₀.gpr .r9).toNat := by
    rw [h1.r19, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (tagLenOk_ok tl19 (s₀.gpr .r9).isLt) fun s₃ ⟨h25, g₃, k₃⟩ => ?_)
  have he₃ := he₁.keep (fun r hr => g₃ r (by revert r; decide) (by revert r; decide)) k₃.sp k₃.rd k₃.wr
  have sv₃ : SavedAt s₃.mem (s₀.gpr .r10) s₀ := k₃.mem ▸ h1.en.saved
  have mid : WP isa (.ite (.zero .d .r25) (.block [.li .r3 0]) (.seq recv (.seq (finTag 0) (cmp 0)))) s₃
      fun s' => Env s₁.gpr s₀.sp s' ∧ SavedAt s'.mem (s₀.gpr .r10) s₀ ∧ VerPost s₀ a ct s' := by
    refine WP.ite _ (eval_zero h25 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hbad : Spec.Gcm.tagLenOk (s₀.gpr .r9).toNat = false := by
        cases e : Spec.Gcm.tagLenOk (s₀.gpr .r9).toNat
        · rfl
        · simp [e] at ht
      have h₀ : WP isa (.block [.li .r3 0]) s₃ fun s' => s'.gpr .r3 = 0 ∧
          (∀ r, r ≠ .r3 → s'.gpr r = s₃.gpr r) ∧ Keeps s₃ s' := by
        crun []
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      refine WP.mono h₀ fun s' ⟨z3, g, k⟩ => ⟨he₃.keep (fun r hr => g r (by revert r; decide)) k.sp k.rd k.wr,
        k.mem ▸ sv₃, fun iv _ _ => ?_⟩
      simp only [hbad, Bool.false_eq_true, false_and, ite_false]
      exact z3
    have hok : Spec.Gcm.tagLenOk (s₀.gpr .r9).toNat = true := by
      cases e : Spec.Gcm.tagLenOk (s₀.gpr .r9).toNat
      · simp [e] at hf
      · rfl
    obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
    have hTr₃ : Covers [⟨s₁.gpr .r20, (s₀.gpr .r9).toNat⟩] (s₃.rd ++ s₃.wr) := by
      rw [k₃.rd, k₃.wr, h1.en.keeps.rd, h1.en.keeps.wr, h1.r20]; exact hTr
    have hTd : (⟨s₁.gpr .r20, (s₀.gpr .r9).toNat⟩ : Region).Disjoint ⟨s₁.gpr .r31 + BitVec.ofNat 64 256, 16⟩ := by
      rw [h1.r20, h1.r31]; exact dT (by decide)
    refine WP.seq (WP.mono (recv_ok he₃ tl19 t1 t16 hTr₃ hTd) fun s₄ ⟨hb₄, hf₄, g₄, k₄⟩ => ?_)
    have he₄ := he₃.keep (fun r hr => g₄ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) k₄.sp k₄.rd k₄.wr
    rw [h1.r31] at hf₄ hb₄
    have f₀₄ : Frame [savedR (s₀.gpr .r10), ⟨s₀.gpr .r10 + BitVec.ofNat 64 256, 16⟩] s₀.mem s₄.mem :=
      (h1.en.frame.mono (by simp)).trans ((k₃.mem ▸ hf₄ : Frame _ s₁.mem s₄.mem).mono (by simp))
    have dc₀₄ : ∀ r ∈ [savedR (s₀.gpr .r10), ⟨s₀.gpr .r10 + BitVec.ofNat 64 256, 16⟩],
        (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L₀.cw'.sub_right (Lay.wSub (by decide))
      · exact L₀.cw'.sub_right (Lay.wSub (by decide))
    have ds₀₄ : ∀ r ∈ [savedR (s₀.gpr .r10), ⟨s₀.gpr .r10 + BitVec.ofNat 64 256, 16⟩],
        (⟨s₀.gpr .r5, 80⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa using (L₀.saved_st (d := 0) (k := 80) (by decide)).symm
      · exact dsw.sub_right (Lay.wSub (by decide))
    have hH₄ : blockAt s₄.mem (s₁.gpr .r29 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .r3) := by
      rw [h1.r29]; exact ctxH_keep f₀₄ dc₀₄
    refine WP.seq (WP.mono (WP.with_rdwr (finTag_ok L (o := 0) (.inl rfl) (a := a) (ct := ct) he₄
      (by rw [h1.r28, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hR hH₄ (by rw [h1.r22]; exact ha)
      (by rw [h1.r23]; exact hP))) fun s₅ ⟨fo, rd₅, wr₅, _⟩ => ?_)
    refine WP.mono (cmp_ok fo.env (o := 0) (.inl rfl) tl19 t1 t16) fun s₇ ⟨h3₇, hf₇, g₇, k₇⟩ => ?_
    have fof := fo.frame
    rw [h1.r30, h1.r31] at fof
    refine ⟨fo.env.keep (fun r hr => g₇ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) k₇.sp k₇.rd k₇.wr, ?_, fun iv hs hl => ?_⟩
    · have sv₅ := (sv₃.frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))).frame fof
        (saved_tagFrame L₀ (.inl rfl))
      rw [h1.r31] at hf₇
      exact sv₅.frame hf₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))
    · have ht' : bytesAt s₅.mem (s₁.gpr .r31 + BitVec.ofNat 64 0) 16 =
          fullTag (ctxCiph s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat) (ctxH s₀.mem (s₀.gpr .r3)) iv a ct :=
        fin_out f₀₄ dc₀₄ ds₀₄ hR h1.r29 h1.r30 h1.r22 fo hs hl
      have hrc : bytesAt s₅.mem (s₁.gpr .r31 + BitVec.ofNat 64 256) 16 =
          bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat ++ zeros (16 - (s₀.gpr .r9).toNat) := by
        rw [h1.r31, bytesAt_frame fof (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl
            · exact ((dsw.sub_right (Lay.wSub (d := 256) (n := 16) (by decide))).sub_left
                (Region.sub_prefix (by decide))).symm
            · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
            · simpa using Lay.w_w (w := s₀.gpr .r10) (a := 256) (n := 16) (d := 0) (k := 16) (.inr (by decide))
                (by decide) (by decide)
            · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), hb₄, k₃.mem,
          ← h1.r20, bytesAt_frame h1.en.frame (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [h1.r20]
            exact dT (d := 128) (k := 120) (by decide)) (by omega), h1.r20]
      have hX : (bytesAt s₅.mem (s₁.gpr .r31 + BitVec.ofNat 64 0) (s₀.gpr .r9).toNat ++
            zeros (16 - (s₀.gpr .r9).toNat) = bytesAt s₅.mem (s₁.gpr .r31 + BitVec.ofNat 64 256) 16) ↔
          (fullTag (ctxCiph s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat) (ctxH s₀.mem (s₀.gpr .r3)) iv a ct).take
            (s₀.gpr .r9).toNat = bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat := by
        rw [bytesAt_take _ _ t16, ht', hrc, List.append_cancel_right_eq]
      simp only [hok, true_and]
      by_cases e : (fullTag (ctxCiph s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat) (ctxH s₀.mem (s₀.gpr .r3)) iv a ct).take
          (s₀.gpr .r9).toNat = bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat
      · simp only [e, ite_true]
        rw [h3₇]; simp only [hX.mpr e, ite_true]
      · simp only [e, ite_false]
        rw [h3₇]; simp only [show ¬ _ from fun x => e (hX.mp x), ite_false]
  refine WP.seq (WP.mono mid fun s₄ ⟨he, sv, vp⟩ => ?_)
  have e31 : s₄.gpr .r31 = s₀.gpr .r10 := (he.fr _ (by decide)).trans h1.r31
  refine WP.mono (restore_ok e31 (by have := he.perm.w; rw [h1.r31] at this; exact Covers.right this) sv
    he.sp (fun r hr => by rw [he.fr r (by revert hr; revert r; decide)]; exact h1.en.low r hr))
    fun s' ⟨ga, _, h3, _⟩ => ⟨ga, fun iv hs hl => ?_⟩
  have := vp iv hs hl
  rw [h3]; exact this

theorem streamVerify_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {s₀ : State} (h : streamVerifyPPC64LE.pre s₀) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ streamVerifyPPC64LE.post s₀ s' := by
  have h' : verPre s₀ := h
  have h₀ := ver_run h' (a := List.replicate ((s₀.gpr .r6).toNat % 16) 0)
    (ct := List.replicate (s₀.gpr .r7).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte =>
      s₀.gpr .r6 = BitVec.ofNat 64 i.1.length ∧ (s₀.gpr .r7).toNat = i.2.length)
    fun i hi => WP.mono (ver_run h' (a := i.1) (ct := i.2) (by rw [hi.1, toNat_mod16]) hi.2) fun _ hh => hh.2)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => by
      have := hh.2 ⟨a, c⟩ ⟨hl, hp⟩ iv hs hl
      simp only at this ⊢
      split <;> simp_all⟩

end VG.Proof.AesGcm.PPC64LE
