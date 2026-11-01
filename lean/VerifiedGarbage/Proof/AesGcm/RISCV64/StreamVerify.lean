module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
import VerifiedGarbage.Proof.AesGcm.RISCV64.FinTag
import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamInit
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_stream_verify`

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/StreamVerify.lean`): the entry saves our caller's
registers and keeps the arguments in `s1`–`s3` and `s8`–`s11` (`ver1_wp`); a tag length
`tagLenOk` rejects returns 0; otherwise `recv` pads the received tag, `finTag 0`
puts the tag into `W` and `cmp 0` compares its first bytes with the
received ones (`ver_run`, `streamVerify_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
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

theorem verLay : Lay (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a7) := by
  obtain ⟨-, -, dcs, dcw, -, dsw, -, fc, fs, -, fw, -, -, a0, a2, a7⟩ := h
  exact Lay.of fc fs fw dcs dcw dsw a0 a2 a7

theorem ver_R : (s₀.gpr .a1).toNat = 10 ∨ (s₀.gpr .a1).toNat = 12 ∨ (s₀.gpr .a1).toNat = 14 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hR, -⟩ := h
  exact hR

theorem ver_al : (s₀.gpr .a7).toNat % 8 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a7⟩ := h
  exact a7

theorem ver_stk : StkOk (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a7) s₀.sp := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h
  exact hk.stk (by simp) (by simp) (by simp)

theorem ver_W : Covers [⟨s₀.gpr .a7, 2560⟩] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

end

/-- After the entry of `verify`, from `s₀`. -/
structure SV1 (s₀ s₁ : State) : Prop where
  en : Entered s₀ (s₀.gpr .a7) s₁
  s0 : s₁.gpr .s0 = s₀.gpr .a7
  s1 : s₁.gpr .s1 = s₀.gpr .a2
  s2 : s₁.gpr .s2 = s₀.gpr .a0
  s3 : s₁.gpr .s3 = s₀.gpr .a1
  s10 : s₁.gpr .s10 = s₀.gpr .a3
  s11 : s₁.gpr .s11 = s₀.gpr .a4
  s9 : s₁.gpr .s9 = s₀.gpr .a5
  s8 : s₁.gpr .s8 = s₀.gpr .a6

theorem ver1_wp {s₀ : State} (hW : Covers [⟨s₀.gpr .a7, 2560⟩] s₀.wr) (hal : (s₀.gpr .a7).toNat % 8 = 0) :
    WP isa (.block verEntry) s₀ (SV1 s₀) := by
  refine WP.block_append (WP.mono (save_ok (b := .a7) hW hal) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e3 : s₁.gpr .a0 = s₀.gpr .a0 := hg _ (by decide)
  have e4 : s₁.gpr .a1 = s₀.gpr .a1 := hg _ (by decide)
  have e5 : s₁.gpr .a2 = s₀.gpr .a2 := hg _ (by decide)
  have e6 : s₁.gpr .a3 = s₀.gpr .a3 := hg _ (by decide)
  have e7 : s₁.gpr .a4 = s₀.gpr .a4 := hg _ (by decide)
  have e8 : s₁.gpr .a5 = s₀.gpr .a5 := hg _ (by decide)
  have e9 : s₁.gpr .a6 = s₀.gpr .a6 := hg _ (by decide)
  crun [Int.reduceNatCast', mov, e3, e4, e5, e6, e7, e8, e9, h31]
  refine ⟨⟨⟨hk.rd, hk.wr, hk.sp⟩, hsv, hf⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [h31]

/-- The environment after the entry. -/
theorem ver_env {s₀ s₁ : State} (h : verPre s₀) (h1 : SV1 s₀ s₁) : Env s₁.gpr s₀.sp s₁ := by
  have hk := ver_stk h
  obtain ⟨hrd, hwr, -⟩ := h
  have perm : Perm (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a7) s₁ :=
    (⟨covers_mem (by rw [hrd]; simp), covers_mem (by rw [hwr]; simp), covers_mem (by rw [hwr]; simp)⟩ :
      Perm (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a7) s₀).of_eq h1.en.keeps.rd h1.en.keeps.wr
  exact ⟨fun _ _ => rfl, h1.en.keeps.sp, by rw [h1.s2, h1.s1, h1.s0]; exact perm,
    by rw [h1.s2, h1.s1, h1.s0, h1.en.keeps.sp]; exact hk⟩

/-- What `verify` promises, for the additional data `a` and the text `ct`. -/
def VerPost (s₀ : State) (a ct : List Byte) (s : State) : Prop :=
  ∀ iv, StreamRepr s₀.mem (s₀.gpr .a2) (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
      (ctxH s₀.mem (s₀.gpr .a0)) iv a ct → s₀.gpr .a3 = BitVec.ofNat 64 a.length →
    let t := fullTag (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat) (ctxH s₀.mem (s₀.gpr .a0)) iv a ct
    if Spec.Gcm.tagLenOk (s₀.gpr .a6).toNat ∧ t.take (s₀.gpr .a6).toNat = bytesAt s₀.mem (s₀.gpr .a5)
        (s₀.gpr .a6).toNat then s.gpr .a0 = 1
    else s.gpr .a0 = 0

theorem ver_run {s₀ : State} (h : verPre s₀) {a ct : List Byte} (ha : a.length % 16 = (s₀.gpr .a3).toNat % 16)
    (hP : (s₀.gpr .a4).toNat = ct.length) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ VerPost s₀ a ct s' := by
  have L₀ := verLay h
  have hR := ver_R h
  have hk₀ := ver_stk h
  have hal : (s₀.gpr .a7).toNat % 8 = 0 := ver_al h
  have hh := h
  obtain ⟨hrd, -, -, -, -, dsw, dtw, -⟩ := hh
  have hTr : Covers [⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩] (s₀.rd ++ s₀.wr) :=
    covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have dT : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩ : Region).Disjoint
      ⟨s₀.gpr .a7 + BitVec.ofNat 64 d, k⟩ := fun hd => dtw.sub_right (Lay.wSub hd)
  refine WP.seq (WP.mono (ver1_wp (ver_W h) hal) fun s₁ h1 => ?_)
  have he₁ := ver_env h h1
  have L := L₀.v h1.s2 h1.s1 h1.s0
  have tl19 : s₁.gpr .s8 = BitVec.ofNat 64 (s₀.gpr .a6).toNat := by
    rw [h1.s8, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (tagLenOk_ok tl19 (s₀.gpr .a6).isLt) fun s₃ ⟨h25, g₃, k₃⟩ => ?_)
  have he₃ := he₁.keep (fun r hr => g₃ r (by revert r; decide) (by revert r; decide)) k₃.sp k₃.rd k₃.wr
  have sv₃ : SavedAt s₃.mem (s₀.gpr .a7) s₀ := k₃.mem ▸ h1.en.saved
  have mid : WP isa (.ite (.zero .s5) (.block [.li .a0 0]) (.seq recv (.seq (finTag 0) (cmp 0)))) s₃
      fun s' => Env s₁.gpr s₀.sp s' ∧ SavedAt s'.mem (s₀.gpr .a7) s₀ ∧ VerPost s₀ a ct s' := by
    refine WP.ite _ (eval_zero h25 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hbad : Spec.Gcm.tagLenOk (s₀.gpr .a6).toNat = false := by
        cases e : Spec.Gcm.tagLenOk (s₀.gpr .a6).toNat
        · rfl
        · simp [e] at ht
      have h₀ : WP isa (.block [.li .a0 0]) s₃ fun s' => s'.gpr .a0 = 0 ∧
          (∀ r, r ≠ .a0 → s'.gpr r = s₃.gpr r) ∧ Keeps s₃ s' := by
        crun [Int.reduceNatCast']
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
      refine WP.mono h₀ fun s' ⟨z3, g, k⟩ => ⟨he₃.keep (fun r hr => g r (by revert r; decide)) k.sp k.rd k.wr,
        k.mem ▸ sv₃, fun iv _ _ => ?_⟩
      simp only [hbad, Bool.false_eq_true, false_and, ite_false]
      exact z3
    have hok : Spec.Gcm.tagLenOk (s₀.gpr .a6).toNat = true := by
      cases e : Spec.Gcm.tagLenOk (s₀.gpr .a6).toNat
      · simp [e] at hf
      · rfl
    obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
    have hTr₃ : Covers [⟨s₁.gpr .s9, (s₀.gpr .a6).toNat⟩] (s₃.rd ++ s₃.wr) := by
      rw [k₃.rd, k₃.wr, h1.en.keeps.rd, h1.en.keeps.wr, h1.s9]; exact hTr
    have hTd : (⟨s₁.gpr .s9, (s₀.gpr .a6).toNat⟩ : Region).Disjoint ⟨s₁.gpr .s0 + BitVec.ofNat 64 256, 16⟩ := by
      rw [h1.s9, h1.s0]; exact dT (by decide)
    refine WP.seq (WP.mono (recv_ok he₃ (by rw [h1.s0]; exact hal) tl19 t1 t16 hTr₃ hTd) fun s₄ ⟨hb₄, hf₄, g₄, k₄⟩ => ?_)
    have he₄ := he₃.keep (fun r hr => g₄ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) k₄.sp k₄.rd k₄.wr
    rw [h1.s0] at hf₄ hb₄
    have f₀₄ : Frame [savedR (s₀.gpr .a7), ⟨s₀.gpr .a7 + BitVec.ofNat 64 256, 16⟩] s₀.mem s₄.mem :=
      (h1.en.frame.mono (by simp)).trans ((k₃.mem ▸ hf₄ : Frame _ s₁.mem s₄.mem).mono (by simp))
    have dc₀₄ : ∀ r ∈ [savedR (s₀.gpr .a7), ⟨s₀.gpr .a7 + BitVec.ofNat 64 256, 16⟩],
        (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L₀.cw'.sub_right (Lay.wSub (by decide))
      · exact L₀.cw'.sub_right (Lay.wSub (by decide))
    have ds₀₄ : ∀ r ∈ [savedR (s₀.gpr .a7), ⟨s₀.gpr .a7 + BitVec.ofNat 64 256, 16⟩],
        (⟨s₀.gpr .a2, 80⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa using (L₀.saved_st (d := 0) (k := 80) (by decide)).symm
      · exact dsw.sub_right (Lay.wSub (by decide))
    have hH₄ : blockAt s₄.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
      rw [h1.s2]; exact ctxH_keep f₀₄ dc₀₄
    refine WP.seq (WP.mono (WP.with_rdwr (finTag_ok L (o := 0) (.inl rfl) (a := a) (ct := ct) he₄
      (by rw [h1.s3, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hR hH₄ (by rw [h1.s10]; exact ha)
      (by rw [h1.s11]; exact hP))) fun s₅ ⟨fo, rd₅, wr₅, _⟩ => ?_)
    refine WP.mono (cmp_ok fo.env (by rw [h1.s0]; exact hal) (o := 0) (.inl rfl) tl19 t1 t16) fun s₇ ⟨h3₇, hf₇, g₇, k₇⟩ => ?_
    have fof := fo.frame
    rw [h1.s1, h1.s0] at fof
    refine ⟨fo.env.keep (fun r hr => g₇ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) k₇.sp k₇.rd k₇.wr, ?_, fun iv hs hl => ?_⟩
    · have sv₅ := (sv₃.frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))).frame fof
        (saved_tagFrame L₀ hk₀ (.inl rfl))
      rw [h1.s0] at hf₇
      exact sv₅.frame hf₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))
    · have ht' : bytesAt s₅.mem (s₁.gpr .s0 + BitVec.ofNat 64 0) 16 =
          fullTag (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat) (ctxH s₀.mem (s₀.gpr .a0)) iv a ct :=
        fin_out f₀₄ dc₀₄ ds₀₄ hR h1.s2 h1.s1 h1.s10 fo hs hl
      have hrc : bytesAt s₅.mem (s₁.gpr .s0 + BitVec.ofNat 64 256) 16 =
          bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat ++ zeros (16 - (s₀.gpr .a6).toNat) := by
        rw [h1.s0, bytesAt_frame fof (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl
            · exact ((dsw.sub_right (Lay.wSub (d := 256) (n := 16) (by decide))).sub_left
                (Region.sub_prefix (by decide))).symm
            · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
            · simpa using Lay.w_w (w := s₀.gpr .a7) (a := 256) (n := 16) (d := 0) (k := 16) (.inr (by decide))
                (by decide) (by decide)
            · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
            · exact hk₀.w.sub_left (Lay.wSub (by decide))) (by decide), hb₄, k₃.mem,
          ← h1.s9, bytesAt_frame h1.en.frame (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [h1.s9]
            exact dT (d := 128) (k := 104) (by decide)) (by omega), h1.s9]
      have hX : (bytesAt s₅.mem (s₁.gpr .s0 + BitVec.ofNat 64 0) (s₀.gpr .a6).toNat ++
            zeros (16 - (s₀.gpr .a6).toNat) = bytesAt s₅.mem (s₁.gpr .s0 + BitVec.ofNat 64 256) 16) ↔
          (fullTag (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat) (ctxH s₀.mem (s₀.gpr .a0)) iv a ct).take
            (s₀.gpr .a6).toNat = bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat := by
        rw [bytesAt_take _ _ t16, ht', hrc, List.append_cancel_right_eq]
      simp only [hok, true_and]
      by_cases e : (fullTag (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat) (ctxH s₀.mem (s₀.gpr .a0)) iv a ct).take
          (s₀.gpr .a6).toNat = bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat
      · simp only [e, ite_true]
        rw [h3₇]; simp only [hX.mpr e, ite_true]
      · simp only [e, ite_false]
        rw [h3₇]; simp only [show ¬ _ from fun x => e (hX.mp x), ite_false]
  refine WP.seq (WP.mono mid fun s₄ ⟨he, sv, vp⟩ => ?_)
  have e31 : s₄.gpr .s0 = s₀.gpr .a7 := (he.fr _ (by decide)).trans h1.s0
  refine WP.mono (restore_ok e31 hal (by have := he.perm.w; rw [h1.s0] at this; exact Covers.right this) sv
    he.sp)
    fun s' ⟨ga, _, h3, _⟩ => ⟨ga, fun iv hs hl => ?_⟩
  have := vp iv hs hl
  rw [h3]; exact this

theorem streamVerify_wp {s₀ : State} (h : streamVerifyRISCV64.pre s₀) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ streamVerifyRISCV64.post s₀ s' := by
  have h' : verPre s₀ := h
  have h₀ := ver_run h' (a := List.replicate ((s₀.gpr .a3).toNat % 16) 0)
    (ct := List.replicate (s₀.gpr .a4).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte =>
      s₀.gpr .a3 = BitVec.ofNat 64 i.1.length ∧ (s₀.gpr .a4).toNat = i.2.length)
    fun i hi => WP.mono (ver_run h' (a := i.1) (ct := i.2) (by rw [hi.1, toNat_mod16]) hi.2) fun _ hh => hh.2)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => by
      have := hh.2 ⟨a, c⟩ ⟨hl, hp⟩ iv hs hl
      simp only at this ⊢
      split <;> simp_all⟩

end VG.Proof.AesGcm.RISCV64
