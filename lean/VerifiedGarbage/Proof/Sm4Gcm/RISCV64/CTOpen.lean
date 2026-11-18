module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.J0
import VerifiedGarbage.Proof.AesGcm.RISCV64.OneShot
import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Seal
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.J0
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OneShot
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Seal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Crypt
public import VerifiedGarbage.Impl.Sm4Gcm.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Crypt
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamCrypt
public import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamCrypt
meta import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTFin
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTFin
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
public import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
meta import VerifiedGarbage.Impl.Sm4Gcm.RISCV64
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamFinish
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamFinish
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-! ### `Sm4Gcm.RISCV64.CTVerify`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.RISCV64.StreamVerify`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_stream_verify`

Untrusted: everything here is checked by Lean. AES-GCM's
(`Proof/AesGcm/RISCV64/StreamVerify.lean`) with SM4's `finTag 0`: the entry
keeps the arguments; `tagLenOk` checks the tag's length; then the received
tag is padded at `W + 256`, the computed one is put into `W` and the two are
compared without a branch (`ver_run`, `streamVerify_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov tagLenOk recv cmp)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel stp_crFrame saved_crFrame ciph_keep tagFrame TagOut TagMid tagLens_ok
  tagArgs_ok ctrTag_mk tagCall_ok tag_ok tFrame_sub t_tagFrame FinOut finTag_ok saved_tagFrame fin_out
  verLay ver_R ver_al ver_stk ver_W SV1 ver1_wp ver_env VerPost ver_run streamVerify_wp verPre
  streamVerifyRISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ghashInput fullTag zeros)
open VG.Spec.Sm4.Gcm (ctxCiph)

section
variable {s₀ : State} (h : verPre s₀)
include h

theorem verLay : Lay (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a6) := by
  obtain ⟨-, -, dcs, dcw, -, dsw, -, fc, fs, -, fw, -, a0, a1, a6⟩ := h
  exact Lay.of fc fs fw dcs dcw dsw a0 a1 a6

theorem ver_al : (s₀.gpr .a6).toNat % 8 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, a6⟩ := h
  exact a6

theorem ver_stk : StkOk (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a6) s₀.sp := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h
  exact hk.stk (by simp) (by simp) (by simp)

theorem ver_big {V : Reg → BitVec 64} (h2 : V .s2 = s₀.gpr .a0) (h1 : V .s1 = s₀.gpr .a1)
    (h0 : V .s0 = s₀.gpr .a6) : Big V s₀.sp := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h
  exact hk.big (by rw [h2]; simp) (by rw [h1]; simp) (by rw [h0]; simp)

theorem ver_bw : (below s₀.sp 3248).Disjoint ⟨s₀.gpr .a6, 2560⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h
  exact hk.buf3 (by simp)

theorem ver_W : Covers [⟨s₀.gpr .a6, 2560⟩] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

end

/-- After the entry of `verify`, from `s₀`. -/
structure SV1 (s₀ s₁ : State) : Prop where
  en : Entered s₀ (s₀.gpr .a6) s₁
  s0 : s₁.gpr .s0 = s₀.gpr .a6
  s1 : s₁.gpr .s1 = s₀.gpr .a1
  s2 : s₁.gpr .s2 = s₀.gpr .a0
  s10 : s₁.gpr .s10 = s₀.gpr .a2
  s11 : s₁.gpr .s11 = s₀.gpr .a3
  s9 : s₁.gpr .s9 = s₀.gpr .a4
  s8 : s₁.gpr .s8 = s₀.gpr .a5

theorem ver1_wp {s₀ : State} (hW : Covers [⟨s₀.gpr .a6, 2560⟩] s₀.wr) (hal : (s₀.gpr .a6).toNat % 8 = 0) :
    WP isa (.block verEntry) s₀ (SV1 s₀) := by
  refine WP.block_append (WP.mono (save_ok (b := .a6) hW hal) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  obtain e3 : s₁.gpr .a0 = s₀.gpr .a0 := hg _ (by decide)
  obtain e4 : s₁.gpr .a1 = s₀.gpr .a1 := hg _ (by decide)
  obtain e5 : s₁.gpr .a2 = s₀.gpr .a2 := hg _ (by decide)
  obtain e6 : s₁.gpr .a3 = s₀.gpr .a3 := hg _ (by decide)
  obtain e7 : s₁.gpr .a4 = s₀.gpr .a4 := hg _ (by decide)
  obtain e8 : s₁.gpr .a5 = s₀.gpr .a5 := hg _ (by decide)
  crun [Int.reduceNatCast', mov, e3, e4, e5, e6, e7, e8, h31]
  refine ⟨⟨⟨hk.rd, hk.wr, hk.sp⟩, hsv, hf⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [h31]

/-- The environment after the entry. -/
theorem ver_env {s₀ s₁ : State} (h : verPre s₀) (h1 : SV1 s₀ s₁) : Env s₁.gpr s₀.sp s₁ := by
  obtain hk := ver_stk h
  obtain ⟨hrd, hwr, -⟩ := h
  obtain perm : Perm (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a6) s₁ :=
    (⟨covers_mem (by rw [hrd]; simp), covers_mem (by rw [hwr]; simp), covers_mem (by rw [hwr]; simp)⟩ :
      Perm (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a6) s₀).of_eq h1.en.keeps.rd h1.en.keeps.wr
  exact ⟨fun _ _ => rfl, h1.en.keeps.sp, by rw [h1.s2, h1.s1, h1.s0]; exact perm,
    by rw [h1.s2, h1.s1, h1.s0, h1.en.keeps.sp]; exact hk⟩

/-- What `verify` promises, for the additional data `a` and the text `ct`. -/
def VerPost (s₀ : State) (a ct : List Byte) (s : State) : Prop :=
  ∀ iv, StreamRepr s₀.mem (s₀.gpr .a1) (ctxCiph s₀.mem (s₀.gpr .a0))
      (ctxH s₀.mem (s₀.gpr .a0)) iv a ct → s₀.gpr .a2 = BitVec.ofNat 64 a.length →
    let t := fullTag (ctxCiph s₀.mem (s₀.gpr .a0)) (ctxH s₀.mem (s₀.gpr .a0)) iv a ct
    if Spec.Gcm.tagLenOk (s₀.gpr .a5).toNat ∧ t.take (s₀.gpr .a5).toNat = bytesAt s₀.mem (s₀.gpr .a4)
        (s₀.gpr .a5).toNat then s.gpr .a0 = 1
    else s.gpr .a0 = 0

theorem ver_run [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : verPre s₀) {a ct : List Byte} (ha : a.length % 16 = (s₀.gpr .a2).toNat % 16)
    (hP : (s₀.gpr .a3).toNat = ct.length) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ VerPost s₀ a ct s' := by
  obtain L₀ := verLay h
  obtain hk₀ := ver_stk h
  obtain hbw := ver_bw h
  obtain hal : (s₀.gpr .a6).toNat % 8 = 0 := ver_al h
  have hh := h
  obtain ⟨hrd, -, -, -, -, dsw, dtw, -⟩ := hh
  obtain hTr : Covers [⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩] (s₀.rd ++ s₀.wr) :=
    covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain dT : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩ : Region).Disjoint
      ⟨s₀.gpr .a6 + BitVec.ofNat 64 d, k⟩ := fun hd => dtw.sub_right (Lay.wSub hd)
  refine WP.seq (WP.mono (ver1_wp (ver_W h) hal) fun s₁ h1 => ?_)
  obtain he₁ := ver_env h h1
  obtain L := L₀.v h1.s2 h1.s1 h1.s0
  obtain tl19 : s₁.gpr .s8 = BitVec.ofNat 64 (s₀.gpr .a5).toNat := by
    rw [h1.s8, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (tagLenOk_ok tl19 (s₀.gpr .a5).isLt) fun s₃ ⟨h25, g₃, k₃⟩ => ?_)
  obtain he₃ := he₁.keep (fun r hr => g₃ r (by revert r; decide) (by revert r; decide)) k₃.sp k₃.rd k₃.wr
  obtain sv₃ : SavedAt s₃.mem (s₀.gpr .a6) s₀ := k₃.mem ▸ h1.en.saved
  obtain mid : WP isa (.ite (.zero .s5) (.block [.li .a0 0]) (.seq recv (.seq (finTag 0) (cmp 0)))) s₃
      fun s' => Env s₁.gpr s₀.sp s' ∧ SavedAt s'.mem (s₀.gpr .a6) s₀ ∧ VerPost s₀ a ct s' := by
    refine WP.ite _ (eval_zero h25 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hbad : Spec.Gcm.tagLenOk (s₀.gpr .a5).toNat = false := by
        cases e : Spec.Gcm.tagLenOk (s₀.gpr .a5).toNat
        · rfl
        · simp [e] at ht
      obtain h₀ : WP isa (.block [.li .a0 0]) s₃ fun s' => s'.gpr .a0 = 0 ∧
          (∀ r, r ≠ .a0 → s'.gpr r = s₃.gpr r) ∧ Keeps s₃ s' := by
        crun [Int.reduceNatCast']
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
      refine WP.mono h₀ fun s' ⟨z3, g, k⟩ => ⟨he₃.keep (fun r hr => g r (by revert r; decide)) k.sp k.rd k.wr,
        k.mem ▸ sv₃, fun iv _ _ => ?_⟩
      simp only [hbad, Bool.false_eq_true, false_and, ite_false]
      exact z3
    obtain hok : Spec.Gcm.tagLenOk (s₀.gpr .a5).toNat = true := by
      cases e : Spec.Gcm.tagLenOk (s₀.gpr .a5).toNat
      · simp [e] at hf
      · rfl
    obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
    obtain hTr₃ : Covers [⟨s₁.gpr .s9, (s₀.gpr .a5).toNat⟩] (s₃.rd ++ s₃.wr) := by
      rw [k₃.rd, k₃.wr, h1.en.keeps.rd, h1.en.keeps.wr, h1.s9]; exact hTr
    obtain hTd : (⟨s₁.gpr .s9, (s₀.gpr .a5).toNat⟩ : Region).Disjoint ⟨s₁.gpr .s0 + BitVec.ofNat 64 256, 16⟩ := by
      rw [h1.s9, h1.s0]; exact dT (by decide)
    refine WP.seq (WP.mono (recv_ok he₃ (by rw [h1.s0]; exact hal) tl19 t1 t16 hTr₃ hTd) fun s₄ ⟨hb₄, hf₄, g₄, k₄⟩ => ?_)
    obtain he₄ := he₃.keep (fun r hr => g₄ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) k₄.sp k₄.rd k₄.wr
    rw [h1.s0] at hf₄ hb₄
    obtain f₀₄ : Frame [savedR (s₀.gpr .a6), ⟨s₀.gpr .a6 + BitVec.ofNat 64 256, 16⟩] s₀.mem s₄.mem :=
      (h1.en.frame.mono (by simp)).trans ((k₃.mem ▸ hf₄ : Frame _ s₁.mem s₄.mem).mono (by simp))
    obtain dc₀₄ : ∀ r ∈ [savedR (s₀.gpr .a6), ⟨s₀.gpr .a6 + BitVec.ofNat 64 256, 16⟩],
        (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L₀.cw'.sub_right (Lay.wSub (by decide))
      · exact L₀.cw'.sub_right (Lay.wSub (by decide))
    obtain ds₀₄ : ∀ r ∈ [savedR (s₀.gpr .a6), ⟨s₀.gpr .a6 + BitVec.ofNat 64 256, 16⟩],
        (⟨s₀.gpr .a1, 80⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa using (L₀.saved_st (d := 0) (k := 80) (by decide)).symm
      · exact dsw.sub_right (Lay.wSub (by decide))
    obtain hH₄ : blockAt s₄.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
      rw [h1.s2]; exact ctxH_keep f₀₄ dc₀₄
    refine WP.seq (WP.mono (WP.with_rdwr (finTag_ok L (ver_big h h1.s2 h1.s1 h1.s0) (o := 0) (.inl rfl) (a := a) (ct := ct) he₄
      hH₄ (by rw [h1.s10]; exact ha)
      (by rw [h1.s11]; exact hP))) fun s₅ ⟨fo, rd₅, wr₅, _⟩ => ?_)
    refine WP.mono (cmp_ok fo.env (by rw [h1.s0]; exact hal) (o := 0) (.inl rfl) tl19 t1 t16) fun s₇ ⟨h3₇, hf₇, g₇, k₇⟩ => ?_
    have fof := fo.frame
    rw [h1.s1, h1.s0] at fof
    refine ⟨fo.env.keep (fun r hr => g₇ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) k₇.sp k₇.rd k₇.wr, ?_, fun iv hs hl => ?_⟩
    · have sv₅ := (sv₃.frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))).frame fof
        (saved_tagFrame L₀ hbw (.inl rfl))
      rw [h1.s0] at hf₇
      exact sv₅.frame hf₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))
    · have ht' : bytesAt s₅.mem (s₁.gpr .s0 + BitVec.ofNat 64 0) 16 =
          fullTag (ctxCiph s₀.mem (s₀.gpr .a0)) (ctxH s₀.mem (s₀.gpr .a0)) iv a ct :=
        fin_out f₀₄ dc₀₄ ds₀₄ h1.s2 h1.s1 h1.s10 fo hs hl
      obtain hrc : bytesAt s₅.mem (s₁.gpr .s0 + BitVec.ofNat 64 256) 16 =
          bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat ++ zeros (16 - (s₀.gpr .a5).toNat) := by
        rw [h1.s0, bytesAt_frame fof (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl
            · exact ((dsw.sub_right (Lay.wSub (d := 256) (n := 16) (by decide))).sub_left
                (Region.sub_prefix (by decide))).symm
            · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
            · simpa using Lay.w_w (w := s₀.gpr .a6) (a := 256) (n := 16) (d := 0) (k := 16) (.inr (by decide))
                (by decide) (by decide)
            · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
            · exact (hbw.sub_right (Lay.wSub (by decide))).symm) (by decide), hb₄, k₃.mem,
          ← h1.s9, bytesAt_frame h1.en.frame (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [h1.s9]
            exact dT (d := 128) (k := 104) (by decide)) (by omega_using []), h1.s9]
      obtain hX : (bytesAt s₅.mem (s₁.gpr .s0 + BitVec.ofNat 64 0) (s₀.gpr .a5).toNat ++
            zeros (16 - (s₀.gpr .a5).toNat) = bytesAt s₅.mem (s₁.gpr .s0 + BitVec.ofNat 64 256) 16) ↔
          (fullTag (ctxCiph s₀.mem (s₀.gpr .a0)) (ctxH s₀.mem (s₀.gpr .a0)) iv a ct).take
            (s₀.gpr .a5).toNat = bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat := by
        rw [bytesAt_take _ _ t16, ht', hrc, List.append_cancel_right_eq]
      simp only [hok, true_and]
      by_cases e : (fullTag (ctxCiph s₀.mem (s₀.gpr .a0)) (ctxH s₀.mem (s₀.gpr .a0)) iv a ct).take
          (s₀.gpr .a5).toNat = bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat
      · simp only [e, ite_true]
        rw [h3₇]; simp only [hX.mpr e, ite_true]
      · simp only [e, ite_false]
        rw [h3₇]; simp only [show ¬ _ from fun x => e (hX.mp x), ite_false]
  refine WP.seq (WP.mono mid fun s₄ ⟨he, sv, vp⟩ => ?_)
  obtain e31 : s₄.gpr .s0 = s₀.gpr .a6 := (he.fr _ (by decide)).trans h1.s0
  refine WP.mono (restore_ok e31 hal (by have := he.perm.w; rw [h1.s0] at this; exact Covers.right this) sv
    he.sp)
    fun s' ⟨ga, _, h3, _⟩ => ⟨ga, fun iv hs hl => ?_⟩
  have := vp iv hs hl
  rw [h3]; exact this

theorem streamVerify_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : streamVerifyRISCV64.pre s₀) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ streamVerifyRISCV64.post s₀ s' := by
  have h' : verPre s₀ := h
  obtain h₀ := ver_run h' (a := List.replicate ((s₀.gpr .a2).toNat % 16) 0)
    (ct := List.replicate (s₀.gpr .a3).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte =>
      s₀.gpr .a2 = BitVec.ofNat 64 i.1.length ∧ (s₀.gpr .a3).toNat = i.2.length)
    fun i hi => WP.mono (ver_run h' (a := i.1) (ct := i.2) (by rw [hi.1, toNat_mod16]) hi.2) fun _ hh => hh.2)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => by
      have := hh.2 ⟨a, c⟩ ⟨hl, hp⟩ iv hs hl
      simp only at this ⊢
      split <;> simp_all⟩

end VG.Proof.Sm4Gcm.RISCV64

end

end

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_stream_verify` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/RISCV64/CTOpen.lean`): the invariant fixes what
`finish`'s does (`FinI`), and the received tag's address and length (`s9`,
`s8`); the branch on the tag length is on that public length, and the
comparison does not branch.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (tagLenOk recv cmp restore)
open VG.Proof.AesGcm.RISCV64 (CT ct_of CT.taintEq Env Lay eval_zero recv_ok cmp_ok tagLenOk_ok tagLenOk_bounds
  restore_taint Keeps covers_mem)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- In `verify`, after the entry: the received tag's `tl` bytes at `Tp`,
apart from `W`, which the state may read. -/
def VerI (c st w sp : Addr) (A T Tp : BitVec 64) (tl : Nat) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s10 = A ∧
    V .s11 = T ∧ V .s9 = Tp ∧ V .s8 = BitVec.ofNat 64 tl ∧ Env V sp s ∧ Big V sp ∧
    Covers [⟨Tp, tl⟩] (s.rd ++ s.wr) ∧ (⟨Tp, tl⟩ : Region).Disjoint ⟨w, 2560⟩

theorem verEntry_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6]) (.block verEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagLenOk_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8]) tagLenOk h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem recv_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s9, .s0]) recv h).isSome =
    true := ⟨_, by taint_decide⟩

theorem cmp_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s0]) (cmp 0) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem li3_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs []) (.block [.li .a0 0]) h).isSome =
    true := ⟨_, by taint_decide⟩

section
variable {c st w sp : Addr} (L : Lay c st w) {A T Tp : BitVec 64} {tl : Nat}
include L

/-- `verify` after the tag length is known to be allowed. -/
theorem verOk_ct [VG.Proof.Gcm.RISCV64.GhashLaw] (t1 : 1 ≤ tl) (t16 : tl ≤ 16) :
    CT (VerI c st w sp A T Tp tl) (.seq recv (.seq (finTag 0) (cmp 0))) := by
  refine CT.seq (J := VerI c st w sp A T Tp tl) ?_ (fun s ⟨V, a, b, d, f, g, i, j, he, hb, hT, hTd⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := recv_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, i₁, j₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, i₂, j₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  · refine WP.mono (recv_ok he (by rw [d]; exact L.wal) j t1 t16 (by rw [i]; exact hT) (by rw [i, d]; exact hTd.sub_right (Lay.wSub
      (by decide)))) fun s' ⟨_, _, hg, hk⟩ => ⟨V, a, b, d, f, g, i, j, he.keep (fun r hr => hg r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) hk.sp hk.rd hk.wr, hb, by rw [hk.rd, hk.wr]; exact hT, hTd⟩
  refine CT.seq (J := VerI c st w sp A T Tp tl)
    ((finTag_ct L (o := 0) (.inl rfl)).mono fun s ⟨V, a, b, d, f, g, _, _, he, hb, _⟩ =>
      ⟨V, a, b, d, f, g, he, hb⟩)
    (fun s ⟨V, a, b, d, f, g, i, j, he, hb, hT, hTd⟩ => WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr
      (finTag_ok (L.v a b d) hb (o := 0)
      (.inl rfl) (a := List.replicate (A.toNat % 16) 0) (ct := List.replicate T.toNat 0) he rfl
      (by simp [f]) (by simp [g]))) fun s' ⟨fo, rd, wr, _⟩ =>
        ⟨V, a, b, d, f, g, i, j, fo.env, hb, by rw [rd, wr]; exact hT, hTd⟩) ?_
  obtain ⟨_, hc⟩ := cmp_taint
  refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, j₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, j₂, h₂, _⟩ =>
    ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
  · rw [h₁.s0, h₂.s0, d₁, d₂]

/-- The same, for correctness: `W` is kept in `s0`. -/
theorem verOk_wp [VG.Proof.Gcm.RISCV64.GhashLaw] (t1 : 1 ≤ tl) (t16 : tl ≤ 16) {s : State} (h : VerI c st w sp A T Tp tl s) :
    WP isa (.seq recv (.seq (finTag 0) (cmp 0))) s fun s' => s'.gpr .s0 = w ∧ s'.sp = sp := by
  obtain ⟨V, a, b, d, f, g, i, j, he, hb, hT, hTd⟩ := h
  refine WP.seq (WP.mono (recv_ok he (by rw [d]; exact L.wal) j t1 t16 (by rw [i]; exact hT) (by rw [i, d]; exact hTd.sub_right (Lay.wSub
    (by decide)))) fun s₁ ⟨_, _, hg, hk⟩ => ?_)
  have he₁ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr
  refine WP.seq (WP.mono (finTag_ok (L.v a b d) hb (o := 0) (.inl rfl) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he₁ rfl (by simp [f]) (by simp [g])) fun s₂ fo => ?_)
  refine WP.mono (cmp_ok fo.env (by rw [d]; exact L.wal) (o := 0) (.inl rfl) j t1 t16) fun s' ⟨_, _, hg', hk'⟩ =>
    ⟨by rw [hg' _ (by decide) (by decide) (by decide) (by decide) (by decide), fo.env.s0, d],
      by rw [hk'.sp, fo.env.sp]⟩

end

theorem streamVerify_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa streamVerifyRISCV64.pre streamVerifyRISCV64.pub streamVerify := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, qsp⟩ := hq
  have h₁' : verPre σ₁ := h₁
  have L := verLay h₁'
  let I₀ : State → Prop := fun s => verPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, q9.symm, qsp.symm⟩, ?_⟩
  let tl := (σ₁.gpr .a5).toNat
  let VI := VerI (σ₁.gpr .a0) (σ₁.gpr .a1) (σ₁.gpr .a6) σ₁.sp (σ₁.gpr .a2) (σ₁.gpr .a3)
    (σ₁.gpr .a4) tl
  refine CT.seq (J := VI) ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := verEntry_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9]⟩) hc
  · refine WP.mono (ver1_wp (ver_W hs) (ver_al hs)) fun s₁ h1 => ?_
    have hT : Covers [⟨s.gpr .a4, (s.gpr .a5).toNat⟩] (s₁.rd ++ s₁.wr) := by
      rw [h1.en.keeps.rd, h1.en.keeps.wr, hs.1]; exact covers_mem (List.mem_append_left _ (by simp))
    have hTd : (⟨s.gpr .a4, (s.gpr .a5).toNat⟩ : Region).Disjoint ⟨s.gpr .a6, 2560⟩ := hs.2.2.2.2.2.2.1
    refine ⟨s₁.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h1.s2, e3]
    · rw [h1.s1, e4]
    · rw [h1.s0, e9]
    · rw [h1.s10, e5]
    · rw [h1.s11, e6]
    · rw [h1.s9, e7]
    · rw [h1.s8, e8, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [← esp]; exact ver_env hs h1
    · rw [← esp]; exact ver_big hs h1.s2 h1.s1 h1.s0
    · simp only [tl]; rw [← e7, ← e8]; exact hT
    · simp only [tl]; rw [← e7, ← e8, ← e9]; exact hTd
  -- the tag length
  let ok := Spec.Gcm.tagLenOk tl
  let J : State → Prop := fun s => VI s ∧ s.gpr .s5 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, f, g, i, j, he, hb, hT, hTd⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, j₁, h₁, _⟩ ⟨_, _, _, _, _, _, _, j₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
  · refine WP.mono (tagLenOk_ok (by rw [he.fr _ (by decide), j]) (σ₁.gpr .a5).isLt) fun s' ⟨h25, hg, hk⟩ =>
      ⟨⟨V, a, b, d, f, g, i, j, he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide))
        hk.sp hk.rd hk.wr, hb, by rw [hk.rd, hk.wr]; exact hT, hTd⟩, h25⟩
  have ev : ∀ s, J s → isa.eval (.zero .s5) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s h => eval_zero h.2 (by split <;> decide)
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a6 ∧ s.sp = σ₁.sp) ?_ (fun s hs => ?_) ?_
  · refine CT.ite _ ev (fun hb => ?_) (fun hb => ?_)
    · obtain ⟨_, hc⟩ := li3_taint
      exact CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, _, _, _, _, _, h₁, _⟩, _⟩ ⟨⟨_, _, _, _, _, _, _, _, h₂, _⟩, _⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => by simp at hr⟩) hc
    · have hok : ok = true := by cases e : ok <;> simp_all
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      exact (verOk_ct L t1 t16).mono fun s h => h.1
  · refine WP.ite _ (ev s hs) (fun hb => ?_) (fun hb => ?_)
    · obtain ⟨⟨V, _, _, d, _, _, _, _, he, _⟩, _⟩ := hs
      have h₀ : WP isa (.block [.li .a0 0]) s fun s' => (∀ r, r ≠ .a0 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
        crun [Int.reduceNatCast']
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₀ fun s' ⟨hg, hk⟩ => ⟨by rw [hg _ (by decide), he.s0, d], by rw [hk.sp, he.sp]⟩
    · have hok : ok = true := by cases e : ok <;> simp_all
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      exact verOk_wp L t1 t16 hs.1
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a6) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.Sm4Gcm.RISCV64

end

end

/-! ### `Sm4Gcm.RISCV64.CTSeal`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.RISCV64.CTOne`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on RISC-V: the pieces of `seal` and `open` are constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/RISCV64/CTSeal.lean`): the invariants fix the context, the
state at `W + 16`, `W`, the stack pointer, the nonce, the additional data
and the data (their addresses and lengths, held in registers the environment
pins or, for the addresses of the additional data and the data, in `W`), and
leave the rest existential; their correctness lemmas carry them from one
piece to the next.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov oneAad dataArgs aadO dataO)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel tagFrame TagOut TagMid tagLens_ok
  tagArgs_ok ctrTag_mk tagCall_ok tag_ok slot_crFrame OC oneCrypt_ok otFrame abs_otSub t_otSub tag_otSub OT
  oneTag_ok
  
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The registers and buffers of `seal` and `open` after the entry: the
context `c`, `W` (with the stack below `sp` apart from them and from the
data), the `n`-byte nonce (length in `s7`), the
additional data (`Ad` in `W + aadO`, length in `s10`) and the data (`D` in
`W + dataO`, length in `s11`). -/
def OneI (c W sp : Addr) (Np : Addr) (n : Nat) (Ad A D Ln : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = W + BitVec.ofNat 64 16 ∧ V .s0 = W ∧
    (Big V sp ∧ (below sp 3248).Disjoint ⟨D, Ln.toNat⟩) ∧ V .s7 = BitVec.ofNat 64 n ∧ V .s10 = A ∧ V .s11 = Ln ∧ Env V sp s ∧
    DataOk (W + BitVec.ofNat 64 16) W s Np n ∧ DataOk (W + BitVec.ofNat 64 16) W s Ad A.toNat ∧
    DataW c (W + BitVec.ofNat 64 16) W s D Ln.toNat ∧ s.mem.readW (W + BitVec.ofNat 64 aadO) 64 = Ad ∧
    s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D

section
variable {c W sp : Addr} {Np : Addr} {n : Nat} {Ad A D Ln : BitVec 64}

/-- `OneI`, after code that keeps the frozen registers, the regions and the
slots of `W`. -/
theorem OneI.keep {s s' : State} (h : OneI c W sp Np n Ad A D Ln s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (ha : s'.mem.readW (W + BitVec.ofNat 64 aadO) 64 = s.mem.readW (W + BitVec.ofNat 64 aadO) 64)
    (hd : s'.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s.mem.readW (W + BitVec.ofNat 64 dataO) 64) :
    OneI c W sp Np n Ad A D Ln s' := by
  obtain ⟨V₀, a, b, d, e, f, i, k, he₀, hN, hA, hD, sa, sd⟩ := h
  have q : ∀ r ∈ frozen, V r = V₀ r := fun r hr => (hV r hr).trans (he₀.fr r hr)
  refine ⟨V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, he, hN.of_eq hrd hwr hsp, hA.of_eq hrd hwr hsp, hD.of_eq hrd hwr hsp,
    ha.trans sa, hd.trans sd⟩
  · rw [q _ (by decide), a]
  · rw [q _ (by decide), b]
  · rw [q _ (by decide), d]
  · exact ⟨⟨e.1.ge, by rw [q .s2 (by decide)]; exact e.1.c, by rw [q .s1 (by decide)]; exact e.1.st,
      by rw [q .s0 (by decide)]; exact e.1.w⟩, e.2⟩
  · rw [q _ (by decide), f]
  · rw [q _ (by decide), i]
  · rw [q _ (by decide), k]

/-- `OneI`, after a block that keeps the frozen registers and the memory. -/
theorem OneI.block {s s' : State} (h : OneI c W sp Np n Ad A D Ln s) (hg : ∀ r ∈ frozen, s'.gpr r = s.gpr r)
    (hk : Keeps s s') : OneI c W sp Np n Ad A D Ln s' := by
  obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := h
  exact ⟨V, a, b, d, e, f, i, k, he.keep hg hk.sp hk.rd hk.wr, hN.of_eq hk.rd hk.wr hk.sp,
    hA.of_eq hk.rd hk.wr hk.sp, hD.of_eq hk.rd hk.wr hk.sp, by rw [hk.mem]; exact sa, by rw [hk.mem]; exact sd⟩

variable (L : Lay c (W + BitVec.ofNat 64 16) W)
include L

omit L in
/-- `OneI` after a piece whose frame is apart from the slots. -/
theorem OneI.frame {s s' : State} (h : OneI c W sp Np n Ad A D Ln s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 248 → ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) :
    OneI c W sp Np n Ad A D Ln s' :=
  h.keep hV he hrd hwr hsp (slot_keep hf (hs (by decide))) (slot_keep hf (hs (by decide)))

/-- Before `oneAad`: the nonce's address and length in `s4` and `s5`. -/
theorem oneAad_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : CT (fun s => OneI c W sp Np n Ad A D Ln s ∧ s.gpr .s4 = Np ∧
    s.gpr .s5 = BitVec.ofNat 64 n) oneAad := by
  -- `j0`
  refine CT.seq (J := fun s => OneI c W sp Np n Ad A D Ln s ∧
    blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) = 0)
    ((j0_ct L (Np := Np) (n := n)).mono fun s ⟨⟨V, a, b, d, _, f, _, _, he, hN, _⟩, h24, h25⟩ =>
      ⟨V, _, a, b, d, ⟨he, rfl, h24, h25, f, by rw [b, d]; exact hN⟩⟩)
    (fun s ⟨hs, h24, h25⟩ => by
      have hs' := hs
      obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
      exact WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr
        (j0_ok (L.v a b d) ⟨he, rfl, h24, h25, f, by rw [b, d]; exact hN⟩)) fun s' ⟨jo, rd, wr, sp'⟩ =>
        ⟨OneI.frame hs
          (fun r hr => (he.fr r hr).symm) jo.env rd wr sp' jo.frame (fun hd' => by
            rw [← d]; exact slot_j0 (L.v a b d) he.stk' hd'), by rw [← b]; exact jo.y⟩) ?_
  -- the additional data's arguments
  refine CT.seq (J := fun s => OneI c W sp Np n Ad A D Ln s ∧
    blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) = 0 ∧ s.gpr .s4 = Ad ∧
    s.gpr .s5 = BitVec.ofNat 64 A.toNat ∧ s.gpr .s6 = BitVec.ofNat 64 0) ?_
    (fun s ⟨hs, hy⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s0, .s10])
        (.block [.load .d .s4 .s0 aadO, mov .s5 .s10, .li .s6 0]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, d₁, _, _, i₁, _, h₁, _⟩, _⟩
      ⟨⟨_, _, _, d₂, _, _, i₂, _, h₂, _⟩, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.s0, h₂.s0, d₁, d₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
  · have hs' := hs
    obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
    have h22 := he.ofNat (r := .s10) (by decide)
    have L' := L.v a b d
    have h₃ : WP isa (.block [.load .d .s4 .s0 aadO, mov .s5 .s10, .li .s6 0]) s fun s₃ =>
        s₃.gpr .s4 = Ad ∧ s₃.gpr .s5 = BitVec.ofNat 64 (V .s10).toNat ∧ s₃.gpr .s6 = BitVec.ofNat 64 0 ∧
          (∀ r, r ≠ .s4 → r ≠ .s5 → r ≠ .s6 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
      refine Steps.wp_ld (off := aadO) (a := V .s0 + BitVec.ofNat 64 aadO) (by decide) (by rw [he.s0])
        (L'.wal8 (by decide) (by decide)) (he.perm.wR (by decide)) fun s₃ u₃ => ?_
      refine Steps.wp_mv fun s₄ u₄ => Steps.wp_li (imm := 0) (by decide) fun s₅ u₅ => WP.block_nil ?_
      refine ⟨by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, d, sa], by
        rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), h22], u₅.gpr, fun r a b c => by
        rw [u₅.other _ c, u₄.other _ b, u₃.other _ a], ⟨?_, ?_, ?_, ?_⟩⟩
      · rw [u₅.mem, u₄.mem, u₃.mem]
      · rw [u₅.rd, u₄.rd, u₃.rd]
      · rw [u₅.wr, u₄.wr, u₃.wr]
      · rw [u₅.sp, u₄.sp, u₃.sp]
    refine WP.mono h₃ fun s₃ ⟨a24, a25, a26, g₃, k₃⟩ =>
      ⟨OneI.block hs
        (fun r hr => g₃ r (by revert r; decide) (by revert r; decide) (by revert r; decide)) k₃,
      by rw [k₃.mem]; exact hy, a24, by rw [a25, i], a26⟩
  -- the additional data absorbed
  refine CT.seq (J := fun s => OneI c W sp Np n Ad A D Ln s) ?_
    (fun s ⟨hs, hy, h24, h25, h26⟩ => ?_) ?_
  · exact (absorb_ct L (yo := 16) (.inr rfl) (D := Ad) (n := A.toNat) (q := 0) (by decide)).mono
      fun s ⟨⟨V, a, b, d, _, _, _, _, he, _, hA, _⟩, _, h24, h25, h26⟩ =>
        ⟨V, blockAt s.mem (V .s2 + BitVec.ofNat 64 240), [], a, b, d, rfl,
          ⟨he, h24, h25, h26, by rw [b, d]; exact hA, rfl⟩⟩
  · have hs' := hs
    obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
    exact WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr (absorb_ok (L.v a b d) (.inr rfl)
      (⟨he, h24, h25, h26, by rw [b, d]; exact hA, rfl⟩ : AbsIn V sp 16 _ [] Ad A.toNat s)))
      fun s' ⟨ab, rd, wr, sp'⟩ => OneI.frame hs (fun r hr => (he.fr r hr).symm) ab.env rd wr sp' ab.frame
        (fun hd' => by rw [← d]; exact slot_abs (L.v a b d) he.stk' hd')
  -- padded
  refine CT.seq (J := fun s => OneI c W sp Np n Ad A D Ln s ∧
    s.gpr .s6 = BitVec.ofNat 64 (A.toNat % 16)) ?_ (fun s hs => ?_)
    ((flush_ct L (yo := 16) (.inr rfl) (q := A.toNat % 16) (Nat.mod_lt _ (by decide))).mono
      fun s ⟨⟨V, a, b, d, _, _, _, _, he, _⟩, h26⟩ => ⟨⟨V, a, b, d, he⟩, h26⟩)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s10])
        (.block [.logicImm .and .s6 .s10 15]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, i₁, _, h₁, _⟩ ⟨_, _, _, _, _, _, i₂, _, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
  · have hs' := hs
    obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
    have h22 := he.fr .s10 (by decide)
    have hand := and15 (V .s10)
    have h₅ : WP isa (.block [.logicImm .and .s6 .s10 15]) s fun s₅ =>
        s₅.gpr .s6 = BitVec.ofNat 64 ((V .s10).toNat % 16) ∧
          (∀ r, r ≠ .s6 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [Int.reduceNatCast', h22, hand]
      exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨a26, g₅, k₅⟩ =>
      ⟨OneI.block hs
        (fun r hr => g₅ r (by revert r; decide)) k₅, by rw [a26, i]⟩

omit L in
theorem dataArgs_ct : CT (OneI c W sp Np n Ad A D Ln) (.block dataArgs) := by
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s11, .s0]) (.block dataArgs)
      h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, k₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, k₂, h₂, _⟩ =>
    ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), k₁, k₂]
  · rw [h₁.s0, h₂.s0, d₁, d₂]

/-- `dataArgs`, for the invariants. -/
theorem dataArgs_one {s : State} (h : OneI c W sp Np n Ad A D Ln s) :
    WP isa (.block dataArgs) s fun s' => OneI c W sp Np n Ad A D Ln s' ∧ s'.gpr .s4 = D ∧
      s'.gpr .s5 = BitVec.ofNat 64 Ln.toNat ∧ s'.gpr .s6 = BitVec.ofNat 64 0 := by
  have hs := h
  obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := h
  exact WP.mono (dataArgs_ok he (by rw [d]; exact L.wal) (by rw [d]; exact sd)) fun s' ⟨a24, a25, a26, g₁, k₁⟩ =>
    ⟨OneI.block hs
      (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide)) k₁,
      a24, by rw [a25, k], a26⟩

theorem oneCrypt_ct : CT (OneI c W sp Np n Ad A D Ln) oneCrypt := by
  refine CT.seq dataArgs_ct (fun s h => dataArgs_one L h)
    ((crypt_ct L (D := D) (n := Ln.toNat) (q := 0)).mono fun s ⟨⟨V, a, b, d, e, _, _, _, he, _, _, hD, _⟩,
      h24, h25, h26⟩ => ⟨V, blockAt s.mem (V .s1 + BitVec.ofNat 64 48), 0, a, b, d, rfl,
        ⟨he, h24, h25, h26, e.1, e.2, by rw [a, b, d]; exact hD⟩⟩)

theorem oneTag_ct [VG.Proof.Gcm.RISCV64.GhashLaw] {o : Nat} (ho : o = 0 ∨ o = 112) :
    CT (OneI c W sp Np n Ad A D Ln) (oneTag o) := by
  refine CT.seq dataArgs_ct (fun s h => dataArgs_one L h) ?_
  refine CT.seq (J := OneI c W sp Np n Ad A D Ln)
    ((absorb_ct L (yo := 16) (.inr rfl) (D := D) (n := Ln.toNat) (q := 0) (by decide)).mono
      fun s ⟨⟨V, a, b, d, _, _, _, _, he, _, _, hD, _⟩, h24, h25, h26⟩ =>
        ⟨V, blockAt s.mem (V .s2 + BitVec.ofNat 64 240), [], a, b, d, rfl,
          ⟨he, h24, h25, h26, by rw [b, d]; exact hD.ok, rfl⟩⟩)
    (fun s ⟨hs, h24, h25, h26⟩ => by
      have hs' := hs
      obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
      exact WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr (absorb_ok (L.v a b d) (.inr rfl)
        (⟨he, h24, h25, h26, by rw [b, d]; exact hD.ok, rfl⟩ : AbsIn V sp 16 _ [] D Ln.toNat s)))
        fun s' ⟨ab, rd, wr, sp'⟩ => OneI.frame hs (fun r hr => (he.fr r hr).symm) ab.env rd wr sp' ab.frame
          (fun hd' => by rw [← d]; exact slot_abs (L.v a b d) he.stk' hd')) ?_
  refine CT.seq (J := fun s => OneI c W sp Np n Ad A D Ln s ∧ s.gpr .s6 = BitVec.ofNat 64 (Ln.toNat % 16)) ?_
    (fun s hs => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s11])
        (.block [.logicImm .and .s6 .s11 15]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, k₁, h₁, _⟩ ⟨_, _, _, _, _, _, _, k₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.fr _ (by decide), h₂.fr _ (by decide), k₁, k₂]
  · have hs' := hs
    obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
    have h23 := he.fr .s11 (by decide)
    have hand := and15 (V .s11)
    have h₅ : WP isa (.block [.logicImm .and .s6 .s11 15]) s fun s₅ =>
        s₅.gpr .s6 = BitVec.ofNat 64 ((V .s11).toNat % 16) ∧
          (∀ r, r ≠ .s6 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [Int.reduceNatCast', h23, hand]
      exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨a26, g₅, k₅⟩ =>
      ⟨OneI.block hs
        (fun r hr => g₅ r (by revert r; decide)) k₅, by rw [a26, k]⟩
  have hq : Ln.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  refine CT.seq (J := OneI c W sp Np n Ad A D Ln)
    ((flush_ct L (yo := 16) (.inr rfl) hq).mono fun s ⟨⟨V, a, b, d, _, _, _, _, he, _⟩, h26⟩ =>
      ⟨⟨V, a, b, d, he⟩, h26⟩)
    (fun s ⟨hs, h26⟩ => by
      have hs' := hs
      obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
      exact WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr (flush_ok (L.v a b d)
        (yo := 16) (.inr rfl) (x := List.replicate (Ln.toNat % 16) 0) ⟨he, rfl⟩ (by simp [h26])))
        fun s' ⟨fl, rd, wr, sp'⟩ => OneI.frame hs (fun r hr => (he.fr r hr).symm) fl.env rd wr sp' fl.frame
          (fun hd' => by rw [← d]; exact slot_t (L.v a b d) he.stk' hd')) ?_
  refine CT.seq (J := EnvB c (W + BitVec.ofNat 64 16) W sp) ?_
    (fun s ⟨V, a, b, d, e, f, i, k, he, _⟩ => ?_) ((tag_ct L ho).mono fun _ h => h)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s10, .s11])
        (.block [mov .s4 .s10, mov .s6 .s11]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, i₁, k₁, h₁, _⟩ ⟨_, _, _, _, _, _, i₂, k₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), k₁, k₂]
  · have h₅ : WP isa (.block [mov .s4 .s10, mov .s6 .s11]) s fun s₅ =>
        (∀ r, r ≠ .s4 → r ≠ .s6 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [Int.reduceNatCast', mov]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨hg, hk⟩ => ⟨V, a, b, d, he.keep (fun r hr => hg r (by revert r; decide)
      (by revert r; decide)) hk.sp hk.rd hk.wr, e.1⟩

end

end VG.Proof.Sm4Gcm.RISCV64

end

end

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_seal` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/RISCV64/CTSeal.lean`): the entry loads `W` from the stack
argument at `sp`, a public address, and then saves our caller's registers
through it: its head is checked on its own, and the rest from the arguments
and `W` (`oneHead_ct`). The pieces follow (`CTOne.lean`), with the tag's
address `T` in `s9`, which the environment pins, and, between them, the
additional data absorbed, for `oneTag 0`.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov oneAad tagOut restore save aadO dataO)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel tagFrame TagOut TagMid tagLens_ok
  tagArgs_ok ctrTag_mk tagCall_ok tag_ok slot_crFrame OC oneCrypt_ok otFrame abs_otSub t_otSub tag_otSub OT
  oneTag_ok stp_crFrame saved_crFrame ciph_keep SO1 one1_wp one_env saved_otFrame sealPre sealRISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The entry of `seal`, from its precondition. -/
theorem sealEntry_wp {s₀ : State} (h : sealPre s₀) :
    WP isa (.block (oneEntry 0)) s₀ fun s₁ =>
      OneI (s₀.gpr .a0) (stackArg s₀ 0) s₀.sp (s₀.gpr .a1) (s₀.gpr .a2).toNat (s₀.gpr .a3)
        (s₀.gpr .a4) (s₀.gpr .a5) (s₀.gpr .a6) s₁ ∧
      s₁.gpr .s4 = s₀.gpr .a1 ∧ s₁.gpr .s5 = BitVec.ofNat 64 (s₀.gpr .a2).toNat ∧
      s₁.gpr .s9 = s₀.gpr .a7 ∧ Covers [⟨s₀.gpr .a7, 16⟩] s₁.wr := by
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, hstk,
    ca, wa⟩ := h
  have hk₀ : StkOk (s₀.gpr .a0) (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0) s₀.sp :=
    one_stk3 hstk (by simp) (by simp)
  have bc₀ : (below s₀.sp 3248).Disjoint ⟨s₀.gpr .a0, 256⟩ := hstk.buf3 (by simp)
  have bw₀ : (below s₀.sp 3248).Disjoint ⟨stackArg s₀ 0, 2560⟩ := hstk.buf3 (by simp)
  have bd₀ : (below s₀.sp 3248).Disjoint ⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩ := hstk.buf3 (by simp)
  have hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW : Covers [⟨stackArg s₀ 0, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hA : Covers [args s₀ 1] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  refine WP.mono (one1_wp (off := 0) (W := stackArg s₀ 0) (.inl rfl) hW wa hstk.1
    (args_in hA (by decide) (i := 0) (by decide)) rfl) fun s₁ h1 => ?_
  have hk₁ := h1.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hDw : Covers [⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩] s₁.wr := by
    rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  refine ⟨⟨s₁.gpr, h1.s2, h1.s1, h1.s0, ⟨⟨hstk.2.1, by rw [h1.s2]; exact bc₀,
      by rw [h1.s1]; exact bw₀.sub_right (Lay.wSub (by decide)), by rw [h1.s0]; exact bw₀⟩, bd₀⟩,
    by rw [h1.s7]; exact toN, h1.s10, h1.s11, one_env h1 hC hW hk₀, ?_, ?_, ⟨⟨covers_left hDw, (s₀.gpr .a6).isLt, fd,
      ddW.sub_right (Lay.wSub (by decide)), ddW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩, hDw, dcd⟩,
    h1.aad, h1.dat⟩, h1.s4, by rw [h1.s5]; exact toN, h1.s9, ?_⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a2).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a4).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · rw [hk₁.wr, hwr]; exact covers_mem (by simp)

/-- The head of the entry: `W`, the stack argument at `sp + off`, into `t1`. -/
theorem oneA_ok {s₀ : State} {off : Nat} {W : Addr} (hoff : off = 0 ∨ off = 8) (hsa : s₀.sp.toNat % 16 = 0)
    (hWi : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 off) 8)
    (hWv : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 off) 64 = W) :
    WP isa (.block [.addSp .t1 0, .load .d .t1 .t1 off]) s₀ fun sA =>
      sA.gpr .t1 = W ∧ (∀ r, r ≠ .t1 → sA.gpr r = s₀.gpr r) ∧ Keeps s₀ sA := by
  refine Steps.wp_addSp (imm := 0) (by decide) fun sA uA => ?_
  refine Steps.wp_ld (off := off) (a := s₀.sp + BitVec.ofNat 64 off) (by omega_using [hoff]) (by rw [uA.gpr, add_ofNat_zero])
    (Spill.al8 (by omega_using [hsa]) (by omega_using [hoff])) (by rw [uA.rd, uA.wr]; exact hWi) fun sB uB => WP.block_nil ?_
  exact ⟨by rw [uB.gpr, uA.mem, hWv], fun r hr => by rw [uB.other r hr, uA.other r hr],
    ⟨by rw [uB.mem, uA.mem], by rw [uB.rd, uA.rd], by rw [uB.wr, uA.wr], by rw [uB.sp, uA.sp]⟩⟩

/-- The rest of the entry, after `W` is in `t1`. -/
abbrev oneRest : List Instr :=
  save .t1 ++ ([mov .s2 .a0, .addi .s1 .s0 16, mov .s4 .a1, mov .s5 .a2, mov .s7 .a2,
    .store .d .a3 .s0 aadO, mov .s10 .a4, .store .d .a5 .s0 dataO, mov .s11 .a6, mov .s9 .a7] : List Instr)

theorem oneEntry_eq (off : Nat) : oneEntry off = ([.addSp .t1 0, .load .d .t1 .t1 off] : List Instr) ++ oneRest := by
  rw [oneEntry, List.append_assoc]

theorem oneHead_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [])
    (.block [.addSp .t1 0, .load .d .t1 .t1 0]) h).isSome = true := ⟨_, by taint_decide⟩

theorem oneRest_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1]) (.block oneRest) h).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {c W sp : Addr} {Np : Addr} {n : Nat} {Ad A D Ln T : BitVec 64}

/-- `OneI`, with the tag's address `T` in `s9`, which the state may write. -/
def OneT (c W sp : Addr) (Np : Addr) (n : Nat) (Ad A D Ln T : BitVec 64) (s : State) : Prop :=
  OneI c W sp Np n Ad A D Ln s ∧ s.gpr .s9 = T ∧ Covers [⟨T, 16⟩] s.wr

theorem OneT.frame {s s' : State} (h : OneT c W sp Np n Ad A D Ln T s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 248 → ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) :
    OneT c W sp Np n Ad A D Ln T s' :=
  ⟨h.1.frame hV he hrd hwr hsp hf hs, (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.1),
    by rw [hwr]; exact h.2.2⟩

/-- Between `oneAad` and `oneTag`: the additional data `a` absorbed and padded. -/
def OneAbs (c W : Addr) (A : BitVec 64) (s : State) : Prop :=
  ∃ H : Block, ∃ a : List Byte, blockAt s.mem (c + BitVec.ofNat 64 240) = H ∧ A.toNat = a.length ∧
    Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length))

variable (L : Lay c (W + BitVec.ofNat 64 16) W) (hTW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 16⟩)
include L hTW

/-- `seal` after its entry. -/
theorem sealBody_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : CT (fun s => OneT c W sp Np n Ad A D Ln T s ∧ s.gpr .s4 = Np ∧
    s.gpr .s5 = BitVec.ofNat 64 n)
    (.seq oneAad (.seq oneCrypt (.seq (oneTag 0) (.seq (.block tagOut) (.block restore))))) := by
  -- `oneAad`
  refine CT.seq (J := fun s => OneT c W sp Np n Ad A D Ln T s ∧ OneAbs c W A s)
    ((oneAad_ct L).mono fun s ⟨⟨hO, _⟩, h24, h25⟩ => ⟨hO, h24, h25⟩)
    (fun s ⟨hT, h24, h25⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr (oneAad_ok (L.v a b d) (A := Ad) he rfl h24 h25 f (by rw [b, d]; exact hN)
      (by rw [b, d, i]; exact hA) (by rw [d]; exact sa))) fun s' ⟨oa, rd, wr, sp'⟩ =>
        ⟨hT.frame (fun r hr => (he.fr r hr).symm) oa.env rd wr sp' oa.frame
          (fun hd' => by rw [← d]; exact slot_j0 (L.v a b d) he.stk' hd'),
        blockAt s.mem (V .s2 + BitVec.ofNat 64 240), bytesAt s.mem Ad (V .s10).toNat,
        by rw [← a]; exact oa.hH, by rw [i, length_bytesAt], by rw [← b]; exact oa.abs⟩
  -- `oneCrypt`
  refine CT.seq (J := fun s => OneT c W sp Np n Ad A D Ln T s ∧ OneAbs c W A s)
    ((oneCrypt_ct L).mono fun s ⟨hT, _⟩ => hT.1) (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have L' := L.v a b d
    have hd : DataW (V .s2) (V .s1) (V .s0) s D (V .s11).toNat := by rw [a, b, d, k]; exact hD
    refine WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr (oneCrypt_ok L' e.1 he hd (by rw [k]; exact e.2) (by rw [d]; exact sd) rfl)) fun s' ⟨oc, rd, wr, sp'⟩ =>
      ⟨hT.frame (fun r hr => (he.fr r hr).symm) oc.env rd wr sp' oc.frame
        (fun hd' => by rw [← d]; exact slot_crFrame L' e.1 hd hd'), H, x, ?_, hl, ?_⟩
    · rw [← a, blockAt_frame oc.frame (fun r hr => (ctx_crFrame L' e.1 hd r hr).sub_left (Lay.ctxSub (by decide)))]
      rw [← a] at hH; exact hH
    · have hx := Nat.mod_lt (x ++ zeros (padLen x.length)).length (show 16 > 0 by decide)
      rw [← b] at hab ⊢
      exact hab.congr (blockAt_frame oc.frame (stp_crFrame e.1.st hd (by decide)))
        (bytesAt_frame oc.frame (stp_crFrame e.1.st hd (by omega_using [])) (by omega_using []))
  -- `oneTag 0`
  refine CT.seq (J := fun s => ∃ V : Reg → BitVec 64, V .s0 = W ∧ V .s9 = T ∧ Env V sp s ∧
    Covers [⟨T, 16⟩] s.wr) ((oneTag_ct L (.inl rfl)).mono fun s ⟨hT, _⟩ => hT.1)
    (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr (oneTag_ok (L.v a b d) e.1 (o := 0) (.inl rfl) (H := H) (a := x) (D := D) he
      (by rw [a]; exact hH) (by rw [i]; exact hl) (by rw [b]; exact hab) (by rw [b, d, k]; exact hD.ok)
      (by rw [d]; exact sd)))
      fun s' ⟨ot, _, wr, _⟩ => ⟨V, d, (he.fr _ (by decide)).symm.trans hT.2.1, ot.env, by rw [wr]; exact hT.2.2⟩
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

theorem seal_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa sealRISCV64.pre sealRISCV64.pub «seal» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩ := hq
  have h₁' : sealPre σ₁ := h₁
  obtain ⟨_, _, _, dcW, _, _, _, _, _, _, _, dtW, _, fc, _, _, _, _, fW, _, _, ca, wa⟩ := h₁'
  let I₀ : State → Prop := fun s => sealPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm,
    q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm⟩, ?_⟩
  refine CT.seq (J := fun s => OneT (σ₁.gpr .a0) (stackArg σ₁ 0) σ₁.sp (σ₁.gpr .a1)
    (σ₁.gpr .a2).toNat (σ₁.gpr .a3) (σ₁.gpr .a4) (σ₁.gpr .a5) (σ₁.gpr .a6) (σ₁.gpr .a7) s ∧
    s.gpr .s4 = σ₁.gpr .a1 ∧ s.gpr .s5 = BitVec.ofNat 64 (σ₁.gpr .a2).toNat) ?_
    (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0⟩ => ?_)
    (sealBody_ct (oneLay fc fW dcW ca wa) (dtW.sub_right (Region.sub_prefix (by decide))))
  · -- the entry: its head loads `W` from a public address, the rest saves through it
    let v : Reg → BitVec 64 := fun r => if r = .t1 then stackArg σ₁ 0 else σ₁.gpr r
    rw [oneEntry_eq]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := oneHead_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea1⟩
      have hA : Covers [args s 1] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hs.1]; simp))
      have hsa : s.sp.toNat % 16 = 0 := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := hs
        exact hk.1
      refine WP.mono (oneA_ok (W := stackArg s 0) (.inl rfl) hsa (args_in hA (by decide) (i := 0) (by decide)) rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea1, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := oneRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  · have := sealEntry_wp hs
    rw [ea0, e3, e4, e5, e6, e7, e8, e9, e10, esp] at this
    exact WP.mono this fun s' ⟨hO, h24, h25, h20, hT⟩ => ⟨⟨hO, h20, hT⟩, h24, h25⟩

end VG.Proof.Sm4Gcm.RISCV64

end

end

/-! ### `Sm4Gcm.RISCV64.Open`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_open`

Untrusted: everything here is checked by Lean. AES-GCM's
(`Proof/AesGcm/RISCV64/Open.lean`) with SM4's pieces: `open` checks the tag
length; if it is allowed, it computes the tag of the ciphertext into
`W + 112` (`oneAad`, `oneTag 112`), copies the received tag to `W + 256` and
compares the first `tag_len` bytes of each (`recv`, `cmp 112`), and decrypts
the data in place only if they are equal; `a0` is the result (`open_wp`).
Until the data is decrypted, everything `open` writes is in the working
space `W` or the stack below `sp` (`Frame (wF W sp)`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov oneAad recv cmp tagLenOk restore dataO)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel stp_crFrame saved_crFrame ciph_keep tagFrame TagOut TagMid tagLens_ok
  tagArgs_ok ctrTag_mk tagCall_ok tag_ok slot_crFrame OC oneCrypt_ok otFrame abs_otSub t_otSub tag_otSub OT
  oneTag_ok SO1 one1_wp one_env saved_otFrame openPre openRes openRISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH fullTag zeros padLen j0 inc32 gctr decryptWith openResult)
open VG.Spec.Sm4.Gcm (ctxCiph)

/-- What `open` promises, given the result `a0` and the data. -/
def OpenPost (s₀ s : State) : Prop :=
  match openRes s₀ with
  | some pt => s.gpr .a0 = 1 ∧ bytesAt s.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = pt
  | none => s.gpr .a0 = 0 ∧ bytesAt s.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat

theorem openPost_none {s₀ s : State} (h : openRes s₀ = none) (h0 : s.gpr .a0 = 0)
    (hd : bytesAt s.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat) :
    OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

theorem openPost_some {s₀ s : State} {pt : List Byte} (h : openRes s₀ = some pt) (h0 : s.gpr .a0 = 1)
    (hd : bytesAt s.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = pt) : OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

/-- What the end of `open` leaves for `restore`. -/
structure OpenOut (s₀ s : State) : Prop where
  s0 : s.gpr .s0 = stackArg s₀ 1
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : SavedAt s.mem (stackArg s₀ 1) s₀
  post : OpenPost s₀ s

/-- An environment for a state's own registers, after a step that changes
only `s8` among those the environment pins. -/
theorem Env.self {V : Reg → BitVec 64} {sp : Addr} {s s' : State} (he : Env V sp s)
    (hg : ∀ r, r ≠ .s8 → s'.gpr r = s.gpr r) (hk : Keeps s s') : Env s'.gpr sp s' :=
  ⟨fun _ _ => rfl, hk.sp.trans he.sp, by
    rw [hg _ (by decide), hg _ (by decide), hg _ (by decide), he.fr _ (by decide), he.fr _ (by decide),
      he.fr _ (by decide)]
    exact he.perm.of_eq hk.rd hk.wr, by
    rw [hg _ (by decide), hg _ (by decide), hg _ (by decide), he.fr _ (by decide), he.fr _ (by decide),
      he.fr _ (by decide), hk.sp]
    exact he.stk⟩

/-- `W` and the stack below `sp`. -/
abbrev wF (W sp : Addr) : List Region := [⟨W, 2560⟩, below sp 3248]

section
variable {W sp : Addr}

/-- What `oneAad`, `oneTag 112`, `recv` and `cmp 112` write is in `W` or below `sp`. -/
theorem inW_j0 : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W sp, ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, by simp, below_sub⟩

theorem inW_ot : ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp, ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem inW_at {d : Nat} (hd : d + 16 ≤ 2560) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 d, 16⟩ : Region)], ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., Lay.wSub hd⟩

theorem inW_one : ∀ r ∈ [oneR W], ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩

/-- The first counter block is apart from what `oneTag 112`, `recv` and `cmp 112` write. -/
theorem cb_ot {c : Addr} (L : Lay c (W + BitVec.ofNat 64 16) W)
    (hbs : (below sp 3248).Disjoint ⟨W + BitVec.ofNat 64 16, 80⟩) :
    ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp ++
      [⟨W + BitVec.ofNat 64 256, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩],
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using Lay.st_st (st := W + BitVec.ofNat 64 16) (a := 48) (n := 16) (d := 0) (k := 48) (.inr (by decide))
      (by decide) (by decide)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact hbs.symm.sub_left (Lay.stSub (by decide))
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)

/-- The slot of the data's address is apart from what `oneTag 112`, `recv` and `cmp 112` write. -/
theorem slot_ot {c : Addr} (L : Lay c (W + BitVec.ofNat 64 16) W) (hbw : (below sp 3248).Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp ++
      [⟨W + BitVec.ofNat 64 256, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩],
      (⟨W + BitVec.ofNat 64 dataO, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (a := 0) (n := 48) (by decide) (.inr ⟨by decide, by decide⟩)).symm.sub_right
      (by simpa using Region.sub_prefix (base := W + BitVec.ofNat 64 16) (show 48 ≤ 48 by decide))
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact hbw.symm.sub_left (Lay.wSub (by decide))
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)

end

/-- A buffer apart from `W` and the stack below `sp` is as it was. -/
theorem bytes_W {m m' : Mem} {W sp p : Addr} {n : Nat} (hf : Frame (wF W sp) m m')
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hs : (⟨p, n⟩ : Region).Disjoint (below sp 3248)) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd
    · exact hs) hn

/-- Whether the computed tag, cut to the tag length, is the received one. -/
abbrev openTagOk (s₀ : State) : Prop :=
  (fullTag (ctxCiph s₀.mem (s₀.gpr .a0)) (ctxH s₀.mem (s₀.gpr .a0))
      (bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat) (bytesAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat)
      (bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat)).take (stackArg s₀ 0).toNat =
    bytesAt s₀.mem (s₀.gpr .a7) (stackArg s₀ 0).toNat

/-- After the tags are compared, with the result in `s8`, from `s₄` (after
the entry). -/
structure OpenMid (s₀ s₄ s : State) : Prop where
  env : Env s.gpr s₀.sp s
  regs : ∀ r ∈ frozen, r ≠ .s8 → s.gpr r = s₄.gpr r
  rd : s.rd = s₄.rd
  wr : s.wr = s₄.wr
  saved : SavedAt s.mem (stackArg s₀ 1) s₀
  frame : Frame (wF (stackArg s₀ 1) s₀.sp) s₀.mem s.mem
  cb : blockAt s.mem (stackArg s₀ 1 + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat))
  dat : s.mem.readW (stackArg s₀ 1 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a5
  s8 : s.gpr .s8 = BitVec.ofNat 64 (if openTagOk s₀ then 1 else 0)

section
variable {s₀ : State} (h : openPre s₀)
include h

theorem openLay : Lay (s₀.gpr .a0) (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) := by
  obtain ⟨-, -, -, dcW, -, -, -, -, -, -, -, -, -, fc, -, -, -, -, fW, -, -, ca, wa⟩ := h
  exact oneLay fc fW dcW ca wa

theorem openStk : StkOk (s₀.gpr .a0) (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₀.sp := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstk, -⟩ := h
  exact one_stk3 hstk (by simp) (by simp)

theorem openGe : 3248 ≤ s₀.sp.toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstk, -⟩ := h
  exact hstk.2.1

theorem openWa : (stackArg s₀ 1).toNat % 8 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, wa⟩ := h
  exact wa

/-- A buffer of the precondition is apart from the stack below `sp`. -/
theorem openBuf {r : Region} (hr : r ∈ [(⟨s₀.gpr .a0, 256⟩ : Region), ⟨s₀.gpr .a1, (s₀.gpr .a2).toNat⟩,
    ⟨s₀.gpr .a3, (s₀.gpr .a4).toNat⟩, ⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩,
    ⟨s₀.gpr .a7, (stackArg s₀ 0).toNat⟩, ⟨stackArg s₀ 1, 2560⟩, args s₀ 2]) :
    r.Disjoint (below s₀.sp 2048) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstk, -⟩ := h
  exact hstk.buf hr

/-- A buffer of the precondition is apart from the 3248 bytes below `sp`. -/
theorem openBuf3 {r : Region} (hr : r ∈ [(⟨s₀.gpr .a0, 256⟩ : Region), ⟨s₀.gpr .a1, (s₀.gpr .a2).toNat⟩,
    ⟨s₀.gpr .a3, (s₀.gpr .a4).toNat⟩, ⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩,
    ⟨s₀.gpr .a7, (stackArg s₀ 0).toNat⟩, ⟨stackArg s₀ 1, 2560⟩, args s₀ 2]) :
    r.Disjoint (below s₀.sp 3248) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstk, -⟩ := h
  exact (hstk.buf3 hr).symm

/-- The registers `open` keeps after its entry, apart from the stack below `sp`. -/
theorem openBig {s : State} (h4 : SO1 (stackArg s₀ 1) s₀ s) : Big s.gpr s₀.sp :=
  ⟨openGe h, by rw [h4.s2]; exact (openBuf3 h (by simp)).symm, by
    rw [h4.s1]; exact (openBuf3 h (r := ⟨stackArg s₀ 1, 2560⟩) (by simp)).symm.sub_right (Lay.wSub (by decide)),
    by rw [h4.s0]; exact (openBuf3 h (by simp)).symm⟩

end

/-- `open`, once the tag length is allowed, up to the comparison of the tags,
followed by any `T`. -/
theorem open_head [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ s₄ : State} (h : openPre s₀) (h4 : SO1 (stackArg s₀ 1) s₀ s₄)
    (h19 : s₄.gpr .s8 = stackArg s₀ 0) (hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true) {T : Prog isa}
    {Q : State → Prop} (k : ∀ s₉, OpenMid s₀ s₄ s₉ → WP isa T s₉ Q) :
    WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .s8 .a0]) T))))) s₄ Q := by
  obtain L₀ := openLay h
  obtain hk₀ := openStk h
  obtain wa := openWa h
  obtain hb₄ := openBig h h4
  have hh := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, -⟩ := hh
  obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
  obtain hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain he₄ := one_env h4 hC hW hk₀
  obtain L := L₀.v h4.s2 h4.s1 h4.s0
  have hk₄ := h4.keeps
  obtain toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  obtain dcF : ∀ r ∈ wF (stackArg s₀ 1) s₀.sp, (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dcW
    · exact (openBuf3 h (by simp))
  obtain F₄ : Frame (wF (stackArg s₀ 1) s₀.sp) s₀.mem s₄.mem := h4.frame.sub inW_one
  -- `oneAad`
  obtain hN : DataOk (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a1) (s₀.gpr .a2).toNat := by
    rw [h4.s1, h4.s0]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a2).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₄.sp]; exact openBuf h (by simp)⟩
  obtain hAd : DataOk (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a3) (s₄.gpr .s10).toNat := by
    rw [h4.s1, h4.s0, h4.s10]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a4).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₄.sp]; exact openBuf h (by simp)⟩
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₄ rfl h4.s4 (by rw [h4.s5]; exact toN)
    (by rw [h4.s7]; exact toN) hN hAd (by rw [h4.s0]; exact h4.aad))) fun s₅ ⟨oa, rd₅, wr₅, sp₅⟩ => ?_)
  have f₅ := oa.frame
  rw [h4.s1, h4.s0] at f₅
  obtain F₅ : Frame (wF (stackArg s₀ 1) s₀.sp) s₀.mem s₅.mem := F₄.trans (f₅.sub inW_j0)
  -- `oneTag 112`
  obtain hDw₄ : Covers [⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩] s₄.wr := by
    rw [hk₄.wr, hwr]; exact covers_mem (by simp)
  obtain hd₄ : DataW (s₄.gpr .s2) (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a5) (s₄.gpr .s11).toNat := by
    rw [h4.s2, h4.s1, h4.s0, h4.s11]
    exact ⟨⟨covers_left hDw₄, (s₀.gpr .a6).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW,
      by rw [hk₄.sp]; exact openBuf h (by simp)⟩, hDw₄, dcd⟩
  obtain dat₅ : s₅.mem.readW (s₄.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a5 := by
    rw [slot_keep oa.frame (slot_j0 L he₄.stk' (by decide)), h4.s0]; exact h4.dat
  refine WP.seq (WP.mono (WP.with_rdwr (oneTag_ok L hb₄ (o := 112) (.inr rfl) oa.env oa.hH
    (length_bytesAt _ _ _).symm oa.abs (hd₄.ok.of_eq rd₅ wr₅ sp₅) dat₅)) fun s₆ ⟨ot, rd₆, wr₆, sp₆⟩ => ?_)
  have f₆ := ot.frame
  rw [h4.s1, h4.s0] at f₆
  obtain F₆ : Frame (wF (stackArg s₀ 1) s₀.sp) s₀.mem s₆.mem := F₅.trans (f₆.sub inW_ot)
  -- `recv`
  obtain h19' : s₄.gpr .s8 = BitVec.ofNat 64 (stackArg s₀ 0).toNat := by rw [h19]; exact toN
  obtain hTr : Covers [⟨s₄.gpr .s9, (stackArg s₀ 0).toNat⟩] (s₆.rd ++ s₆.wr) := by
    rw [rd₆, wr₆, rd₅, wr₅, hk₄.rd, hk₄.wr, h4.s9]
    exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain hTd : (⟨s₄.gpr .s9, (stackArg s₀ 0).toNat⟩ : Region).Disjoint ⟨s₄.gpr .s0 + BitVec.ofNat 64 256, 16⟩ := by
    rw [h4.s9, h4.s0]; exact dtW.sub_right (Lay.wSub (by decide))
  obtain wa₄ : (s₄.gpr .s0).toNat % 8 = 0 := by rw [h4.s0]; exact wa
  refine WP.seq (WP.mono (recv_ok ot.env wa₄ h19' t1 t16 hTr hTd) fun s₇ ⟨hb₇, hf₇, g₇, k₇⟩ => ?_)
  obtain he₇ := ot.env.keep (fun r hr => g₇ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₇.sp k₇.rd k₇.wr
  rw [h4.s0] at hf₇ hb₇
  obtain F₇ : Frame (wF (stackArg s₀ 1) s₀.sp) s₀.mem s₇.mem := F₆.trans (hf₇.sub (inW_at (by decide)))
  -- `cmp 112`
  refine WP.seq (WP.mono (cmp_ok he₇ wa₄ (o := 112) (.inr rfl) h19' t1 t16) fun s₈ ⟨h3₈, hf₈, g₈, k₈⟩ => ?_)
  obtain he₈ := he₇.keep (fun r hr => g₈ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₈.sp k₈.rd k₈.wr
  rw [h4.s0] at hf₈ h3₈
  obtain F₈ : Frame (wF (stackArg s₀ 1) s₀.sp) s₀.mem s₈.mem := F₇.trans (hf₈.sub (inW_at (by decide)))
  -- what the tags are
  let iv := bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat
  let a := bytesAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat
  let tg := bytesAt s₀.mem (s₀.gpr .a7) (stackArg s₀ 0).toNat
  let ciph := ctxCiph s₀.mem (s₀.gpr .a0)
  let H := ctxH s₀.mem (s₀.gpr .a0)
  obtain hH₄ : blockAt s₄.mem (s₄.gpr .s2 + BitVec.ofNat 64 240) = H := by
    rw [h4.s2]; exact ctxH_keep F₄ dcF
  obtain iv₄ : bytesAt s₄.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat = iv :=
    bytes_W F₄ dnW (openBuf3 h (by simp)) (by have := (s₀.gpr .a2).isLt; omega_arith)
  obtain a₄ : bytesAt s₄.mem (s₀.gpr .a3) (s₄.gpr .s10).toNat = a := by
    rw [h4.s10]; exact bytes_W F₄ daW (openBuf3 h (by simp)) (by have := (s₀.gpr .a4).isLt; omega_arith)
  obtain ct₅ : bytesAt s₅.mem (s₀.gpr .a5) (s₄.gpr .s11).toNat = ct := by
    rw [h4.s11]; exact bytes_W F₅ ddW (openBuf3 h (by simp)) (by have := (s₀.gpr .a6).isLt; omega_arith)
  obtain hc₅ : ciphOf s₅.mem (s₄.gpr .s2) = ciph := by rw [h4.s2]; exact ciph_keep F₅ dcF
  obtain hj₅ : blockAt s₅.mem (s₄.gpr .s1) = j0 H iv := by rw [oa.j, hH₄, iv₄]
  obtain hT₆ : bytesAt s₆.mem (stackArg s₀ 1 + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    have ho := ot.out
    rw [h4.s0, hc₅, hj₅, ct₅, ← h4.s0, hH₄, a₄, ← Proof.Gcm.fullTag_eq] at ho
    rw [← h4.s0]; exact ho
  obtain hT₇ : bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    rw [bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)]
    exact hT₆
  obtain hr₇ : bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 256) 16 = tg ++ zeros (16 - (stackArg s₀ 0).toNat) := by
    rw [hb₇, h4.s9]; congr 1; exact bytes_W F₆ dtW (openBuf3 h (by simp)) (by omega_arith)
  let X := (fullTag ciph H iv a ct).take (stackArg s₀ 0).toNat = tg
  obtain hX : (bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 112) (stackArg s₀ 0).toNat ++
      zeros (16 - (stackArg s₀ 0).toNat) = bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 256) 16) ↔ X := by
    rw [bytesAt_take _ _ t16, hT₇, hr₇, List.append_cancel_right_eq]
  obtain r3₈ : s₈.gpr .a0 = if X then 1 else 0 := by
    rw [h3₈]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  obtain f₆₈ : Frame (otFrame (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) 112 s₀.sp ++
      [⟨stackArg s₀ 1 + BitVec.ofNat 64 256, 16⟩, ⟨stackArg s₀ 1 + BitVec.ofNat 64 272, 16⟩]) s₅.mem s₈.mem :=
    ((f₆.mono fun r hr => List.mem_append_left _ hr).trans (hf₇.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp)).trans (hf₈.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp)
  obtain cb₈ : blockAt s₈.mem (stackArg s₀ 1 + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
    rw [blockAt_frame f₆₈ (cb_ot L₀ (by rw [← h4.s1]; exact (openBig h h4).st)), ← h4.s1, oa.cb, hH₄, iv₄]
  obtain dat₈ : s₈.mem.readW (stackArg s₀ 1 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a5 := by
    rw [slot_keep f₆₈ (slot_ot L₀ (openBuf3 h (by simp)).symm), ← h4.s0]; exact dat₅
  obtain sv₈ : SavedAt s₈.mem (stackArg s₀ 1) s₀ :=
    (((h4.saved.frame f₅ (saved_j0Frame L₀ hk₀)).frame f₆ (saved_otFrame L₀ (openBuf3 h (by simp)).symm (.inr rfl))).frame hf₇
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))).frame
      hf₈ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))
  -- the result into `s8`
  refine WP.seq (Steps.wp_mv fun s₉ u₉ => WP.block_nil ?_)
  obtain k₉ : Keeps s₈ s₉ := ⟨u₉.mem, u₉.rd, u₉.wr, u₉.sp⟩
  obtain he₉ := Env.self he₈ u₉.other k₉
  obtain e : ∀ r ∈ frozen, r ≠ .s8 → s₉.gpr r = s₄.gpr r := fun r hf hr => (u₉.other r hr).trans (he₈.fr r hf)
  obtain rd₉ : s₉.rd = s₄.rd := k₉.rd.trans (k₈.rd.trans (k₇.rd.trans (rd₆.trans rd₅)))
  obtain wr₉ : s₉.wr = s₄.wr := k₉.wr.trans (k₈.wr.trans (k₇.wr.trans (wr₆.trans wr₅)))
  refine k s₉ ⟨he₉, e, rd₉, wr₉, k₉.mem ▸ sv₈, k₉.mem ▸ F₈, by rw [k₉.mem]; exact cb₈, by rw [k₉.mem]; exact dat₈,
    ?_⟩
  rw [u₉.gpr, r3₈]
  show _ = BitVec.ofNat 64 (if X then 1 else 0)
  by_cases hx : X
  · simp only [eq_true hx, ite_true]; rfl
  · simp only [eq_false hx, ite_false]; rfl

/-- `open` from the comparison's result on. -/
theorem open_tail {s₀ s₄ s₉ : State} (h : openPre s₀) (h4 : SO1 (stackArg s₀ 1) s₀ s₄)
    (hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true) (om : OpenMid s₀ s₄ s₉) :
    WP isa (.seq (.ite (.zero .s8) (.block []) oneCrypt) (.block [mov .a0 .s8])) s₉ (OpenOut s₀) := by
  obtain L₀ := openLay h
  obtain hk₀ := openStk h
  have hh := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, -⟩ := hh
  have hk₄ := h4.keeps
  obtain toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  obtain dcF : ∀ r ∈ wF (stackArg s₀ 1) s₀.sp, (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dcW
    · exact (openBuf3 h (by simp))
  obtain hDw₄ : Covers [⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩] s₄.wr := by
    rw [hk₄.wr, hwr]; exact covers_mem (by simp)
  obtain hd₄ : DataW (s₄.gpr .s2) (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a5) (s₄.gpr .s11).toNat := by
    rw [h4.s2, h4.s1, h4.s0, h4.s11]
    exact ⟨⟨covers_left hDw₄, (s₀.gpr .a6).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW,
      by rw [hk₄.sp]; exact openBuf h (by simp)⟩, hDw₄, dcd⟩
  let iv := bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat
  let ciph := ctxCiph s₀.mem (s₀.gpr .a0)
  let H := ctxH s₀.mem (s₀.gpr .a0)
  have he₉ := om.env
  have e := om.regs
  have rd₉ := om.rd
  have wr₉ := om.wr
  have sv₉ := om.saved
  have F₉ := om.frame
  obtain sp₉ : s₉.sp = s₄.sp := he₉.sp.trans hk₄.sp.symm
  obtain dat₉ : bytesAt s₉.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = ct :=
    bytes_W F₉ ddW (openBuf3 h (by simp)) (by have := (s₀.gpr .a6).isLt; omega_arith)
  obtain hd₉₀ : DataW (s₀.gpr .a0) (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₉ (s₀.gpr .a5)
      (s₀.gpr .a6).toNat := by
    have := hd₄.of_eq rd₉ wr₉ sp₉
    rwa [h4.s2, h4.s1, h4.s0, h4.s11] at this
  -- the data decrypted only if the tags are equal
  obtain mid : WP isa (.ite (.zero .s8) (.block []) oneCrypt) s₉ fun s₁₀ =>
      Env s₉.gpr s₀.sp s₁₀ ∧ SavedAt s₁₀.mem (stackArg s₀ 1) s₀ ∧ s₁₀.rd = s₄.rd ∧ s₁₀.wr = s₄.wr ∧
      ((openTagOk s₀) → bytesAt s₁₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = gctr ciph (inc32 (j0 H iv)) ct) ∧
      (¬(openTagOk s₀) → bytesAt s₁₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = ct) := by
    refine WP.ite _ (eval_zero om.s8 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hx : ¬(openTagOk s₀) := fun x => by simp [x] at ht
      exact WP.block_nil ⟨he₉, sv₉, rd₉, wr₉, fun x => absurd x hx, fun _ => dat₉⟩
    · have hx : (openTagOk s₀) := Classical.byContradiction fun x => by simp [x] at hf
      obtain L₉ : Lay (s₉.gpr .s2) (s₉.gpr .s1) (s₉.gpr .s0) := by
        rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide), h4.s2, h4.s1,
          h4.s0]
        exact L₀
      obtain hd₉ : DataW (s₉.gpr .s2) (s₉.gpr .s1) (s₉.gpr .s0) s₉ (s₀.gpr .a5) (s₉.gpr .s11).toNat := by
        rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide),
          e _ (by decide) (by decide)]
        exact hd₄.of_eq rd₉ wr₉ sp₉
      obtain hb₉ : Big s₉.gpr s₀.sp := by
        obtain hb := openBig h h4
        exact ⟨hb.ge, by rw [e _ (by decide) (by decide)]; exact hb.c, by rw [e _ (by decide) (by decide)]; exact hb.st,
          by rw [e _ (by decide) (by decide)]; exact hb.w⟩
      obtain hbd₉ : (below s₀.sp 3248).Disjoint ⟨s₀.gpr .a5, (s₉.gpr .s11).toNat⟩ := by
        rw [e _ (by decide) (by decide), h4.s11]; exact (openBuf3 h (by simp)).symm
      obtain cb₉ : blockAt s₉.mem (s₉.gpr .s1 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
        rw [e _ (by decide) (by decide), h4.s1]; exact om.cb
      obtain ds₉ : s₉.mem.readW (s₉.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a5 := by
        rw [e _ (by decide) (by decide), h4.s0]; exact om.dat
      refine WP.mono (WP.with_rdwr (oneCrypt_ok L₉ hb₉ he₉ hd₉ hbd₉ ds₉ cb₉)) fun s₁₀ ⟨oc, rd₁₀, wr₁₀, _⟩ => ?_
      have cf := oc.frame
      rw [e _ (by decide) (by decide), e _ (by decide) (by decide), h4.s1, h4.s11] at cf
      refine ⟨oc.env, sv₉.frame cf (saved_crFrame L₀ (openBuf3 h (by simp)).symm hd₉₀), rd₁₀.trans rd₉, wr₁₀.trans wr₉, fun _ => ?_,
        fun x => absurd hx x⟩
      have ho := oc.out
      rw [e _ (by decide) (by decide), e _ (by decide) (by decide), h4.s11, h4.s2, ciph_keep F₉ dcF, dat₉] at ho
      exact ho
  refine WP.seq (WP.mono mid fun s₁₀ ⟨he₁₀, sv₁₀, rd₁₀, wr₁₀, hd₁, hd₂⟩ => ?_)
  -- the result back into `a0`
  refine Steps.wp_mv fun s₁₁ u₁₁ => WP.block_nil ?_
  obtain r3₁₁ : s₁₁.gpr .a0 = if (openTagOk s₀) then 1 else 0 := by
    rw [u₁₁.gpr, he₁₀.fr _ (by decide), om.s8]
    by_cases hx : openTagOk s₀
    · simp only [eq_true hx, ite_true]; rfl
    · simp only [eq_false hx, ite_false]; rfl
  obtain hres : openRes s₀ = if (openTagOk s₀) then some (gctr ciph (inc32 (j0 H iv)) ct) else none := by
    simp only [openRes, openResult, hok, ite_true, decryptWith]; rfl
  refine ⟨by rw [u₁₁.other _ (by decide), he₁₀.fr _ (by decide), e _ (by decide) (by decide), h4.s0],
    by rw [u₁₁.sp]; exact he₁₀.sp, by rw [u₁₁.rd, rd₁₀, hk₄.rd], by rw [u₁₁.wr, wr₁₀, hk₄.wr],
    by rw [u₁₁.mem]; exact sv₁₀, ?_⟩
  by_cases hx : (openTagOk s₀)
  · exact openPost_some (hres.trans (ite_eq_left_of_eq_true _ _ (eq_true hx)))
      (r3₁₁.trans (ite_eq_left_of_eq_true _ _ (eq_true hx))) (by rw [u₁₁.mem]; exact hd₁ hx)
  · exact openPost_none (hres.trans (ite_eq_right_of_eq_false _ _ (eq_false hx)))
      (r3₁₁.trans (ite_eq_right_of_eq_false _ _ (eq_false hx))) (by rw [u₁₁.mem]; exact hd₂ hx)

theorem open_good [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ s₄ : State} (h : openPre s₀) (h4 : SO1 (stackArg s₀ 1) s₀ s₄)
    (h19 : s₄.gpr .s8 = stackArg s₀ 0) (hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true) :
    WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .s8 .a0])
      (.seq (.ite (.zero .s8) (.block []) oneCrypt) (.block [mov .a0 .s8]))))))) s₄ (OpenOut s₀) :=
  open_head h h4 h19 hok fun _ om => open_tail h h4 hok om

/-- The contract's postcondition, from `OpenPost`, through `restore`. -/
theorem openPost_out {s₀ s s' : State} (op : OpenPost s₀ s) (hm : s'.mem = s.mem) (h3 : s'.gpr .a0 = s.gpr .a0) :
    openRISCV64.post s₀ s' := by
  unfold OpenPost at op
  unfold openRISCV64
  dsimp only
  rw [hm, h3]
  split <;> rename_i heq <;> rw [heq] at op <;> exact ⟨by rw [op.1]; rfl, op.2⟩

/-- After a step that changes no register the entry set but `t0` and `s8`. -/
theorem SO1.keep {W : Addr} {s₀ s₁ s₂ : State} (h1 : SO1 W s₀ s₁)
    (hg : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .s8 → s₂.gpr r = s₁.gpr r) (hk : Keeps s₁ s₂) : SO1 W s₀ s₂ :=
  ⟨⟨hk.rd.trans h1.keeps.rd, hk.wr.trans h1.keeps.wr, hk.sp.trans h1.keeps.sp⟩, hk.mem ▸ h1.saved,
    hk.mem ▸ h1.frame, hk.mem ▸ h1.aad, hk.mem ▸ h1.dat,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s0, by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s1,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s2,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s4, by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s5,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s7, by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s10,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s11, by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s9⟩

/-- The entry of `open`, and `tag_len` in `s8`. -/
theorem openEntry_wp {s₀ : State} (h : openPre s₀) :
    WP isa (.block openEntry) s₀ fun s₂ =>
      SO1 (stackArg s₀ 1) s₀ s₂ ∧ s₂.gpr .s8 = stackArg s₀ 0 := by
  obtain wa := openWa h
  have hh := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, hstk,
    -⟩ := hh
  obtain hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hA : Covers [args s₀ 2] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain dA : (args s₀ 2).Disjoint (oneR (stackArg s₀ 1)) :=
    (dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).symm
  obtain hLd : (⟨s₀.sp + BitVec.ofNat 64 0, 8⟩ : Region).Disjoint (oneR (stackArg s₀ 1)) :=
    dA.sub_left (Region.sub_prefix (show 8 ≤ 8 * 2 by decide))
  unfold openEntry
  refine WP.block_append (WP.mono (one1_wp (off := 8) (W := stackArg s₀ 1)
    (.inr rfl) hW wa hstk.1 (args_in hA (by decide) (i := 1) (by decide)) rfl) fun s₁ h1 => ?_)
  -- `tag_len` into `s8`
  refine Steps.wp_addSp (imm := 0) (by decide) fun sA uA => ?_
  obtain hi : InRegions (sA.rd ++ sA.wr) (s₀.sp + BitVec.ofNat 64 0) 8 := by
    rw [uA.rd, uA.wr, h1.keeps.rd, h1.keeps.wr]; exact args_in hA (by decide) (i := 0) (by decide)
  obtain hv : sA.mem.readW (s₀.sp + BitVec.ofNat 64 0) 64 = stackArg s₀ 0 := by
    rw [uA.mem, Frame.readW h1.frame (r := ⟨s₀.sp + BitVec.ofNat 64 0, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hLd) (by decide)]
    rfl
  refine Steps.wp_ld (off := 0) (a := s₀.sp + BitVec.ofNat 64 0) (by decide)
    (by rw [uA.gpr, h1.keeps.sp, add_ofNat_zero]) (Spill.al8 (by have := hstk.1; omega_using [this]) (by decide)) hi fun s₂ u₂ => WP.block_nil ?_
  exact ⟨h1.keep (fun r _ ht hr => by rw [u₂.other r hr, uA.other r ht])
    ⟨by rw [u₂.mem, uA.mem], by rw [u₂.rd, uA.rd], by rw [u₂.wr, uA.wr], by rw [u₂.sp, uA.sp]⟩,
    by rw [u₂.gpr, hv]⟩

theorem open_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : openRISCV64.pre s₀) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧ openRISCV64.post s₀ s' := by
  have h' : openPre s₀ := h
  obtain wa := openWa h'
  obtain hk₀ := openStk h'
  have hh := h'
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, -⟩ := hh
  obtain hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  unfold «open»
  refine WP.seq (WP.mono (openEntry_wp h') fun s₂ ⟨h2, h19⟩ => ?_)
  -- the tag length
  obtain h19' : s₂.gpr .s8 = BitVec.ofNat 64 (stackArg s₀ 0).toNat := by rw [h19]; simp
  refine WP.seq (WP.mono (tagLenOk_ok h19' (stackArg s₀ 0).isLt) fun s₃ ⟨h25, g₃, k₃⟩ => ?_)
  obtain F₂ : Frame (wF (stackArg s₀ 1) s₀.sp) s₀.mem s₂.mem := h2.frame.sub inW_one
  obtain mid : WP isa (.ite (.zero .s5) (.block [.li .a0 0]) openGood) s₃ (OpenOut s₀) := by
    refine WP.ite _ (eval_zero h25 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hbad : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = false := by
        cases e : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat
        · rfl
        · simp [e] at ht
      refine Steps.wp_li (imm := 0) (by decide) fun s' u => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [u.other _ (by decide), g₃ _ (by decide) (by decide)]; exact h2.s0
      · rw [u.sp, k₃.sp]; exact h2.keeps.sp
      · rw [u.rd, k₃.rd]; exact h2.keeps.rd
      · rw [u.wr, k₃.wr]; exact h2.keeps.wr
      · rw [u.mem, k₃.mem]; exact h2.saved
      · refine openPost_none (by simp only [openRes, openResult, hbad]; rfl) u.gpr ?_
        rw [u.mem, k₃.mem]
        exact bytes_W F₂ ddW (openBuf3 h' (by simp)) (by have := (s₀.gpr .a6).isLt; omega_arith)
    · have hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true := by
        cases e : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat
        · simp [e] at hf
        · rfl
      refine WP.seq (Steps.wp_mv fun s₄ u₄ => WP.block_nil ?_)
      obtain g₄ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .s8 → s₄.gpr r = s₂.gpr r := fun r h0 _ h19 => by
        by_cases e : r = .s5
        · subst e
          rw [u₄.gpr, g₃ _ (by decide) (by decide), h2.s7, h2.s5]
        · rw [u₄.other r e, g₃ r h0 e]
      obtain h4 : SO1 (stackArg s₀ 1) s₀ s₄ :=
        h2.keep g₄ ⟨by rw [u₄.mem, k₃.mem], by rw [u₄.rd, k₃.rd], by rw [u₄.wr, k₃.wr], by rw [u₄.sp, k₃.sp]⟩
      exact open_good h' h4 (by rw [u₄.other _ (by decide), g₃ _ (by decide) (by decide)]; exact h19) hok
  refine WP.seq (WP.mono mid fun s₅ oo => ?_)
  refine WP.mono (restore_ok oo.s0 wa (by rw [oo.rd, oo.wr]; exact Covers.right hW) oo.saved oo.sp)
    fun s' ⟨ga, hm, h3, _⟩ => ⟨ga, openPost_out oo.post hm h3⟩

end VG.Proof.Sm4Gcm.RISCV64

end

end

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_open` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/RISCV64/CTOpen.lean`): the entry as for `seal`
(`CTSeal.lean`), then `tag_len` (`s8`), public, and the two branches of
`tagLenOk`. Once the tag length is allowed, the data is decrypted only if
the tags are equal, which may differ between two runs only as the result
does (the contract's `pub`: whether it succeeds). The invariants of the
pieces up to that comparison carry what the rest of each run reaches
(`CT.seqG`, from `open_head`): the result in `s8`, which is then the same in
both runs.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov oneAad tagLenOk recv cmp restore aadO dataO)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel tagFrame TagOut TagMid tagLens_ok
  tagArgs_ok ctrTag_mk tagCall_ok tag_ok slot_crFrame OC oneCrypt_ok otFrame abs_otSub t_otSub tag_otSub OT
  oneTag_ok stp_crFrame saved_crFrame ciph_keep SO1 one1_wp one_env saved_otFrame sealPre sealRISCV64
  openPre openRes openRISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- Two runs of `c₁` carry what a further `R` reaches from them. -/
theorem CT.seqG {I J Z : State → Prop} {c₁ R c₂ : Prog isa} (h₁ : CT I c₁) (w : ∀ s, I s → WP isa c₁ s J)
    (h₂ : CT (fun s => J s ∧ WP isa R s Z) c₂) : CT (fun s => I s ∧ WP isa (.seq c₁ R) s Z) (.seq c₁ c₂) :=
  CT.seq (h₁.mono fun _ h => h.1) (fun s h => WP.mono (WP.forall_det (w s h.1) (P := fun _ : Unit => True)
    (Q := fun _ s' => WP isa R s' Z) fun _ _ => WP.seq_iff.mp h.2) fun _ h => ⟨h.1, h.2 () trivial⟩) h₂

theorem openRes_isSome {t : State} (hok : Spec.Gcm.tagLenOk (stackArg t 0).toNat = true) :
    (openRes t).isSome = decide (openTagOk t) := by
  have e : openRes t = if openTagOk t then
      some (Spec.Gcm.gctr (Spec.Sm4.Gcm.ctxCiph t.mem (t.gpr .a0))
        (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH t.mem (t.gpr .a0)) (bytesAt t.mem (t.gpr .a1) (t.gpr .a2).toNat)))
        (bytesAt t.mem (t.gpr .a5) (t.gpr .a6).toNat)) else none := by
    simp only [openRes, Spec.Gcm.openResult, hok, ite_true, Spec.Gcm.decryptWith]
  rw [e]
  by_cases h : openTagOk t
  · simp only [eq_true h, ite_true, decide_true, Option.isSome_some]
  · simp only [eq_false h, ite_false, decide_false, Option.isSome_none]

theorem openHead_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [])
    (.block [.addSp .t1 0, .load .d .t1 .t1 8]) h).isSome = true := ⟨_, by taint_decide⟩

theorem openRest_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1])
    (.block (oneRest ++ ([.addSp .t1 0, .load .d .s8 .t1 0] : List Instr))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagLenOk_taint' : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8]) tagLenOk h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp112_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s0]) (cmp 112) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem nil_taint (b : List Instr) (h : b = [.li .a0 0] ∨ b = [mov .s5 .s7] ∨ b = [mov .s8 .a0] ∨
    b = [mov .a0 .s8]) : ∃ hh, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs []) (.block b) hh).isSome = true := by
  rcases h with rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `OneI`, with the tag's address `T` and length `TL` in `s9` and `s8`. -/
def OneO (c W sp : Addr) (Np : Addr) (n : Nat) (Ad A D Ln T TL : BitVec 64) (s : State) : Prop :=
  OneI c W sp Np n Ad A D Ln s ∧ s.gpr .s9 = T ∧ s.gpr .s8 = TL ∧ Covers [⟨T, TL.toNat⟩] (s.rd ++ s.wr)

section
variable {c W sp : Addr} {Np : Addr} {n : Nat} {Ad A D Ln T TL : BitVec 64}

theorem OneO.frame {s s' : State} (h : OneO c W sp Np n Ad A D Ln T TL s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 248 → ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) :
    OneO c W sp Np n Ad A D Ln T TL s' :=
  ⟨h.1.frame hV he hrd hwr hsp hf hs, (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.1),
    (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.2.1), by rw [hrd, hwr]; exact h.2.2.2⟩

/-- `OneI` after a step that changes only `s8` among the registers it pins. -/
theorem OneI.self {s s' : State} (h : OneI c W sp Np n Ad A D Ln s) (hg : ∀ r, r ≠ .s8 → s'.gpr r = s.gpr r)
    (hk : Keeps s s') : OneI c W sp Np n Ad A D Ln s' := by
  obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := h
  have q : ∀ r ∈ frozen, r ≠ .s8 → s'.gpr r = V r := fun r hr h19 => (hg r h19).trans (he.fr r hr)
  refine ⟨s'.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Env.self he hg hk, hN.of_eq hk.rd hk.wr hk.sp,
    hA.of_eq hk.rd hk.wr hk.sp, hD.of_eq hk.rd hk.wr hk.sp, by rw [hk.mem]; exact sa, by rw [hk.mem]; exact sd⟩
  · rw [q _ (by decide) (by decide), a]
  · rw [q _ (by decide) (by decide), b]
  · rw [q _ (by decide) (by decide), d]
  · exact ⟨⟨e.1.ge, by rw [q .s2 (by decide) (by decide)]; exact e.1.c,
      by rw [q .s1 (by decide) (by decide)]; exact e.1.st, by rw [q .s0 (by decide) (by decide)]; exact e.1.w⟩, e.2⟩
  · rw [q _ (by decide) (by decide), f]
  · rw [q _ (by decide) (by decide), i]
  · rw [q _ (by decide) (by decide), k]

/-- The result of the comparison in `s8`, for `b`. -/
abbrev Res (b : Bool) (s : State) : Prop := s.gpr .s8 = BitVec.ofNat 64 (if b then 1 else 0)

/-- The slots of the addresses are apart from what `oneTag 112` writes. -/
theorem slot_ot112 (L : Lay c (W + BitVec.ofNat 64 16) W) (hbw : (below sp 3248).Disjoint ⟨W, 2560⟩) {d : Nat}
    (hd : 232 ≤ d ∧ d + 8 ≤ 248) :
    ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (a := 0) (n := 48) (by decide) (.inr ⟨by omega_using [hd], by omega_using [hd]⟩)).symm.sub_right
      (by simpa using Region.sub_prefix (base := W + BitVec.ofNat 64 16) (show 48 ≤ 48 by decide))
  · exact Lay.w_w (.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact hbw.symm.sub_left (Lay.wSub (by omega_using [hd]))

/-- The slots are apart from a block of `W` at `e ≥ 248`. -/
theorem slot_at {e : Nat} (he : 248 ≤ e) (he' : e + 16 ≤ 2560) {d : Nat} (hd : 232 ≤ d ∧ d + 8 ≤ 248) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 e, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact Lay.w_w (.inl (by omega_using [he, hd])) (by omega_using [hd]) he'

variable (L : Lay c (W + BitVec.ofNat 64 16) W)
  (hTd : (⟨T, TL.toNat⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩) (t1 : 1 ≤ TL.toNat) (t16 : TL.toNat ≤ 16)
  (b : Bool)
include L hTd t1 t16

/-- `open` from `oneAad` on, once the tag length is allowed, with what the
comparison of the tags gives (`Res b`). -/
theorem openGood_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : CT (fun s => (OneO c W sp Np n Ad A D Ln T TL s ∧ s.gpr .s4 = Np ∧
    s.gpr .s5 = BitVec.ofNat 64 n) ∧ WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112)
      (.seq (.block [mov .s8 .a0]) (.block [])))))) s (Res b))
    (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .s8 .a0])
      (.seq (.ite (.zero .s8) (.block []) oneCrypt) (.block [mov .a0 .s8]))))))) := by
  -- `oneAad`
  refine CT.seqG (J := fun s => OneO c W sp Np n Ad A D Ln T TL s ∧ OneAbs c W A s)
    ((oneAad_ct L).mono fun s ⟨⟨hO, _⟩, h24, h25⟩ => ⟨hO, h24, h25⟩)
    (fun s ⟨hT, h24, h25⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr (oneAad_ok (L.v a b d) (A := Ad) he rfl h24 h25 f (by rw [b, d]; exact hN)
      (by rw [b, d, i]; exact hA) (by rw [d]; exact sa))) fun s' ⟨oa, rd, wr, sp'⟩ =>
        ⟨hT.frame (fun r hr => (he.fr r hr).symm) oa.env rd wr sp' oa.frame
          (fun hd' => by rw [← d]; exact slot_j0 (L.v a b d) he.stk' hd'),
        blockAt s.mem (V .s2 + BitVec.ofNat 64 240), bytesAt s.mem Ad (V .s10).toNat,
        by rw [← a]; exact oa.hH, by rw [i, length_bytesAt], by rw [← b]; exact oa.abs⟩
  -- `oneTag 112`
  refine CT.seqG (J := OneO c W sp Np n Ad A D Ln T TL) ((oneTag_ct L (.inr rfl)).mono fun s ⟨hT, _⟩ => hT.1)
    (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have hk : (below sp 3248).Disjoint ⟨W, 2560⟩ := by rw [← d]; exact e.1.w
    exact WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr (oneTag_ok (L.v a b d) e.1 (o := 112) (.inr rfl) (H := H) (a := x) (D := D) he
      (by rw [a]; exact hH) (by rw [i]; exact hl) (by rw [b]; exact hab) (by rw [b, d, k]; exact hD.ok)
      (by rw [d]; exact sd)))
      fun s' ⟨ot, rd, wr, sp'⟩ => hT.frame (fun r hr => (he.fr r hr).symm) ot.env rd wr sp'
        (by have := ot.frame; rw [b, d] at this; exact this) (fun hd' => slot_ot112 L hk hd')
  -- `recv`
  refine CT.seqG (J := OneO c W sp Np n Ad A D Ln T TL) ?_ (fun s hT => ?_) ?_
  · obtain ⟨_, hc⟩ := recv_taint
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, d₁, _, _, _, _, h₁, _⟩, a₁, b₁, _⟩
      ⟨⟨_, _, _, d₂, _, _, _, _, h₂, _⟩, a₂, b₂, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [b₁, b₂]
    · rw [a₁, a₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have h19 : V .s8 = BitVec.ofNat 64 TL.toNat := by rw [← he.fr _ (by decide), hT.2.2.1]; simp
    have h20 : V .s9 = T := by rw [← he.fr _ (by decide), hT.2.1]
    exact WP.mono (recv_ok he (by rw [d]; exact L.wal) h19 t1 t16 (by rw [h20]; exact hT.2.2.2)
      (by rw [h20, d]; exact hTd))
      fun s' ⟨_, hf', g', k'⟩ => hT.frame (fun r hr => (he.fr r hr).symm) (he.keep (fun r hr => g' r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) k'.sp k'.rd k'.wr) k'.rd k'.wr k'.sp hf'
        (fun hd' => by rw [d]; exact slot_at (by decide) (by decide) hd')
  -- `cmp 112`
  refine CT.seqG (J := OneO c W sp Np n Ad A D Ln T TL) ?_ (fun s hT => ?_) ?_
  · obtain ⟨_, hc⟩ := cmp112_taint
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, d₁, _, _, _, _, h₁, _⟩, _, b₁, _⟩
      ⟨⟨_, _, _, d₂, _, _, _, _, h₂, _⟩, _, b₂, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [b₁, b₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have h19 : V .s8 = BitVec.ofNat 64 TL.toNat := by rw [← he.fr _ (by decide), hT.2.2.1]; simp
    exact WP.mono (cmp_ok he (by rw [d]; exact L.wal) (o := 112) (.inr rfl) h19 t1 t16)
      fun s' ⟨_, hf', g', k'⟩ => hT.frame (fun r hr => (he.fr r hr).symm) (he.keep (fun r hr => g' r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) k'.sp k'.rd k'.wr) k'.rd k'.wr k'.sp hf'
        (fun hd' => by rw [d]; exact slot_at (by decide) (by decide) hd')
  -- the result into `s8`
  refine CT.seqG (J := OneI c W sp Np n Ad A D Ln) ?_ (fun s hT => ?_) ?_
  · obtain ⟨_, hc⟩ := nil_taint [mov .s8 .a0] (.inr (.inr (.inl rfl)))
    exact CT.taintEq _ (fun _ => 0) sp (fun s ⟨⟨_, _, _, _, _, _, _, _, h₁, _⟩, _⟩ => ⟨h₁.sp, by simp⟩) hc
  · exact Steps.wp_mv fun s' u => WP.block_nil (hT.1.self u.other ⟨u.mem, u.rd, u.wr, u.sp⟩)
  -- the data decrypted only if the tags are equal, which both runs agree on
  have ev : ∀ s, OneI c W sp Np n Ad A D Ln s ∧ WP isa (.block []) s (Res b) →
      isa.eval (.zero .s8) s = some (decide ((if b then 1 else 0) = 0)) := fun s h =>
    eval_zero (WP.block_nil_iff.mp h.2) (by split <;> decide)
  refine CT.seq (J := fun s => s.gpr .s0 = W ∧ s.sp = sp)
    (CT.ite _ ev (fun _ => CT.skip) (fun _ => (oneCrypt_ct L).mono fun s h => h.1)) (fun s h => ?_) ?_
  · obtain ⟨V, a, b', d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := h.1
    refine WP.ite _ (ev s h) (fun _ => WP.block_nil_iff.mpr ⟨by rw [he.s0, d], he.sp⟩) (fun _ => ?_)
    exact WP.mono (oneCrypt_ok (L.v a b' d) e.1 he (by rw [a, b', d, k]; exact hD) (by rw [k]; exact e.2) (by rw [d]; exact sd) rfl)
      fun s' oc => ⟨by rw [oc.env.s0, d], oc.env.sp⟩
  · obtain ⟨_, hc⟩ := nil_taint [mov .a0 .s8] (.inr (.inr (.inr rfl)))
    exact CT.taintEq _ (fun _ => 0) sp (fun s ⟨_, hsp⟩ => ⟨hsp, by simp⟩) hc

end

/-- `mv s5, s7` after `tagLenOk`: the entry's registers again. -/
theorem mov25_so1 {W : Addr} {t₀ s₂ s₃ s₄ : State} (h2 : SO1 W t₀ s₂)
    (g : ∀ r, r ≠ .t0 → r ≠ .s5 → s₃.gpr r = s₂.gpr r) (k : Keeps s₂ s₃) (u : Steps.Upd s₃ s₄ .s5 (s₃.gpr .s7)) :
    SO1 W t₀ s₄ ∧ s₄.gpr .s8 = s₂.gpr .s8 := by
  refine ⟨h2.keep (fun r h0 _ _ => ?_) ⟨by rw [u.mem, k.mem], by rw [u.rd, k.rd], by rw [u.wr, k.wr],
    by rw [u.sp, k.sp]⟩, by rw [u.other _ (by decide), g _ (by decide) (by decide)]⟩
  by_cases e : r = .s5
  · subst e
    rw [u.gpr, g _ (by decide) (by decide), h2.s7, h2.s5]
  · rw [u.other r e, g r h0 e]

/-- After the entry (and `s5` restored), what the pieces need. -/
theorem open_one {t₀ s : State} (h : openPre t₀) (h1 : SO1 (stackArg t₀ 1) t₀ s)
    (h19 : s.gpr .s8 = stackArg t₀ 0) :
    OneO (t₀.gpr .a0) (stackArg t₀ 1) t₀.sp (t₀.gpr .a1) (t₀.gpr .a2).toNat (t₀.gpr .a3)
        (t₀.gpr .a4) (t₀.gpr .a5) (t₀.gpr .a6) (t₀.gpr .a7) (stackArg t₀ 0) s ∧
      s.gpr .s4 = t₀.gpr .a1 ∧ s.gpr .s5 = BitVec.ofNat 64 (t₀.gpr .a2).toNat := by
  have hk₀ := openStk h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, hstk,
    -⟩ := id h
  have hC : Covers [⟨t₀.gpr .a0, 256⟩] (t₀.rd ++ t₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW : Covers [⟨stackArg t₀ 1, 2560⟩] t₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hk₁ := h1.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hDw : Covers [⟨t₀.gpr .a5, (t₀.gpr .a6).toNat⟩] s.wr := by
    rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  refine ⟨⟨⟨s.gpr, h1.s2, h1.s1, h1.s0, ⟨openBig h h1, (openBuf3 h (by simp)).symm⟩, by rw [h1.s7]; exact toN,
    h1.s10, h1.s11,
    one_env h1 hC hW hk₀, ?_, ?_, ⟨⟨covers_left hDw, (t₀.gpr .a6).isLt, fd,
      ddW.sub_right (Lay.wSub (by decide)), ddW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩, hDw, dcd⟩,
    h1.aad, h1.dat⟩, h1.s9, h19, ?_⟩, h1.s4, by rw [h1.s5]; exact toN⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (t₀.gpr .a2).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (t₀.gpr .a4).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp))

theorem open_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa openRISCV64.pre openRISCV64.pub «open» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩, qres⟩ := hq
  have h₁' : openPre σ₁ := h₁
  obtain ⟨_, _, _, dcW, _, _, _, _, _, _, _, dtW, _, fc, _, _, _, _, fW, _, _, ca, wa⟩ := h₁'
  let I₀ : State → Prop := fun s => openPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1 ∧ (openRes s).isSome = (openRes σ₁).isSome
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm,
    q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm,
    (qa 1 (by decide)).symm, qres.symm⟩, ?_⟩
  -- the entry: its head loads `W` from a public address, the rest saves through it
  let J₁ : State → Prop := fun s => ∃ t₀, I₀ t₀ ∧ SO1 (stackArg t₀ 1) t₀ s ∧
    s.gpr .s8 = stackArg t₀ 0
  refine CT.seq (J := J₁) ?_ (fun s hs => WP.mono (openEntry_wp hs.1) fun s' ⟨a, b⟩ => ⟨s, hs, a, b⟩) ?_
  · let v : Reg → BitVec 64 := fun r => if r = .t1 then stackArg σ₁ 1 else σ₁.gpr r
    have hl : openEntry = [.addSp .t1 0, .load .d .t1 .t1 8] ++
        (oneRest ++ ([.addSp .t1 0, .load .d .s8 .t1 0] : List Instr)) := by
      rw [openEntry, oneEntry_eq, List.append_assoc]
    rw [hl]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := openHead_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, _, ea2, _⟩
      have hA : Covers [args s 2] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hs.1]; simp))
      have hsa : s.sp.toNat % 16 = 0 := (openStk hs).al
      refine WP.mono (oneA_ok (W := stackArg s 1) (.inr rfl) hsa (args_in hA (by decide) (i := 1) (by decide)) rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea2, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := openRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  -- the tag length
  let ok := Spec.Gcm.tagLenOk (stackArg σ₁ 0).toNat
  let J₂ : State → Prop := fun s => ∃ t₀ s₂, I₀ t₀ ∧ SO1 (stackArg t₀ 1) t₀ s₂ ∧
    s₂.gpr .s8 = stackArg t₀ 0 ∧ (∀ r, r ≠ .t0 → r ≠ .s5 → s.gpr r = s₂.gpr r) ∧ Keeps s₂ s ∧
    s.gpr .s5 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J₂) ?_ (fun s ⟨t₀, ht, h1, h19⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint'
    exact CT.taintEq _ (fun _ => stackArg σ₁ 0) σ₁.sp (fun s ⟨t₀, ht, h1, h19⟩ =>
      ⟨h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1, by simp [h19, ht.2.2.2.2.2.2.2.2.2.2.1]⟩) hc
  · have h19' : s.gpr .s8 = BitVec.ofNat 64 (stackArg t₀ 0).toNat := by rw [h19]; simp
    refine WP.mono (tagLenOk_ok h19' (stackArg t₀ 0).isLt) fun s' ⟨h25, g, k⟩ =>
      ⟨t₀, s, ht, h1, h19, g, k, ?_⟩
    rw [h25, ht.2.2.2.2.2.2.2.2.2.2.1]
  -- the two branches, then `restore`
  have ev : ∀ s, J₂ s → isa.eval (.zero .s5) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s ⟨_, _, _, _, _, _, _, h25⟩ => eval_zero h25 (by split <;> decide)
  have L₀ := oneLay fc fW dcW ca wa
  refine CT.seq (J := fun s => s.gpr .s0 = stackArg σ₁ 1 ∧ s.sp = σ₁.sp) (CT.ite _ ev (fun _ => ?_) (fun hb => ?_))
    (fun s hs => ?_) ?_
  · obtain ⟨_, hc⟩ := nil_taint [.li .a0 0] (.inl rfl)
    exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
      ⟨k.sp.trans (h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
  · have hok : ok = true := by
      cases e : ok
      · simp [e] at hb
      · rfl
    obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
    refine CT.seq ?_ (fun s ⟨t₀, s₂, ht, h1, h19, g, k, _⟩ => ?_)
      (openGood_ct (sp := σ₁.sp) (Np := σ₁.gpr .a1) (n := (σ₁.gpr .a2).toNat) (Ad := σ₁.gpr .a3) (A := σ₁.gpr .a4)
        (D := σ₁.gpr .a5) (Ln := σ₁.gpr .a6) L₀ (dtW.sub_right (Lay.wSub (by decide))) t1 t16
        (openRes σ₁).isSome)
    · obtain ⟨_, hc⟩ := nil_taint [mov .s5 .s7] (.inr (.inl rfl))
      exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
        ⟨k.sp.trans (h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
    · obtain ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, eres⟩ := ht
      refine Steps.wp_mv fun s₄ u => WP.block_nil ?_
      obtain ⟨h4, h19₄⟩ := mov25_so1 h1 g k u
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 0).toNat = true := by rw [ea0]; exact hok
      have o := open_one hpre h4 (h19₄.trans h19)
      rw [e3, e4, e5, e6, e7, e8, e9, e10, ea0, ea1, esp] at o
      refine ⟨o, open_head hpre h4 (h19₄.trans h19) hok₀ (T := .block []) fun s₉ om => WP.block_nil_iff.mpr ?_⟩
      show s₉.gpr .s8 = _
      rw [om.s8, ← eres, openRes_isSome hok₀]
      by_cases hx : openTagOk t₀
      · simp only [eq_true hx, ite_true, decide_true]
      · simp only [eq_false hx, ite_false, decide_false, Bool.false_eq_true]
  · obtain ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, eres⟩, h1, h19, g, k, h25⟩ := hs
    refine WP.ite _ (ev s ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, eres⟩, h1, h19, g, k, h25⟩)
      (fun ht => ?_) (fun hf => ?_)
    · exact Steps.wp_li (imm := 0) (by decide) fun s' u => WP.block_nil
        ⟨by rw [u.other _ (by decide), g _ (by decide) (by decide), h1.s0, ea1],
          by rw [u.sp, k.sp, h1.keeps.sp, esp]⟩
    · have hok : ok = true := by
        cases e : ok
        · simp [e] at hf
        · rfl
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 0).toNat = true := by rw [ea0]; exact hok
      refine WP.seq (Steps.wp_mv fun s₄ u => WP.block_nil ?_)
      obtain ⟨h4, h19₄⟩ := mov25_so1 h1 g k u
      exact WP.mono (open_good hpre h4 (h19₄.trans h19) hok₀) fun s' oo =>
        ⟨by rw [oo.s0, ea1], by rw [oo.sp, esp]⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq _ (fun _ => stackArg σ₁ 1) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.Sm4Gcm.RISCV64
