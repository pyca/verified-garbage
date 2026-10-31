module

import VerifiedGarbage.Proof.AesSiv.PPC64LE.Rel
public import VerifiedGarbage.Proof.AesSiv.PPC64LE.MacCT
import VerifiedGarbage.Proof.AesSiv.PPC64LE.CtrCT
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Rel
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
meta import VerifiedGarbage.Proof.AesSiv.PPC64LE.Rel
meta import VerifiedGarbage.Proof.AesSiv.PPC64LE.MacCT
meta import VerifiedGarbage.Proof.AesSiv.PPC64LE.CtrCT
meta import VerifiedGarbage.Proof.AesSiv.PPC64LE.Dec
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Rel
meta import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.AesSiv.PPC64LE.Fn
import VerifiedGarbage.Proof.AesSiv.PPC64LE.Long
meta import VerifiedGarbage.Proof.AesSiv.PPC64LE.Enc
meta import VerifiedGarbage.Proof.AesSiv.PPC64LE.Fn
meta import VerifiedGarbage.Proof.AesSiv.PPC64LE.Long
public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Enc
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# AES-SIV on PPC64LE: constant time of `encrypt` and `decrypt`

Untrusted: everything here is checked by Lean. Two runs from the same public
arguments (`Args c`) with the same descriptors (`DescAgree`) leak the same:
the entry and the code between the pieces by the taint analysis, the pieces
by `MacCT.lean` and `CtrCT.lean`, each from what the correctness proofs
establish of both runs (`rel_seqR`, `Runs.of_wp`). `decrypt` compares the
IVs and masks the data without a branch, so its result is not leaked.
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.Impl.AesSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor Upd Mupd
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_taint)
open VG.Proof.AesCcm.PPC64LE (Runs Runs.of_wp rel_seqR)
open VG.Proof.CmacAes.Stream.PPC64LE (FArgs)
open VG.Spec.Aes (bytesAt)

/-- The entry, S2V's first state and its call. -/
theorem entryStart_wp {c : Cx} {s : State} (Ar : Args c s) (hA : Ads c s.mem s) :
    WP isa (.seq (.block (entry ++ startPre)) Impl.CmacAes.Stream.PPC64LE.finCall) s fun s₂ =>
      ∃ s₁, Entered c s s₁ ∧ AInv c s₁ 0 s₂ := by
  have L := Ar.lay
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (entry_wp Ar) fun s₁ En => ?_))
  have E₁ := En.env
  refine WP.mono (WP.seq_iff.mp (start_wp L E₁)) fun s₂' h => WP.mono h fun s₂ ⟨K₂, f₂, d₂⟩ => ⟨s₁, En, ?_⟩
  have wf₁ : WF c s.mem s₁.mem := WF.of En.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  exact { env := E₁.of_pk K₂.pk
          pk := K₂.pk
          ads := (wf₁.ads L hA).of_eq (by rw [K₂.pk.rd, En.rd]) (by rw [K₂.pk.wr, En.wr])
          r17 := by rw [K₂.r17, En.r17, Nat.mul_zero, BitVec.add_zero]
          r18 := by rw [K₂.r18, En.r18, Nat.sub_zero]
          frame := f₂
          acc := by rw [d₂, List.take_zero]; rfl }

/-- The entry and S2V's first state in two runs. -/
theorem entryStart_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (A₁ : Args c σ₁) (A₂ : Args c σ₂)
    (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block (entry ++ startPre)) Impl.CmacAes.Stream.PPC64LE.finCall) TT := by
  have W {σ : State} (A : Args c σ) : WP isa (.block (entry ++ startPre)) σ fun s =>
      ∃ s₁, Entered c σ s₁ ∧ s.sp = σ.sp ∧
        FArgs s c.C (c.W + BitVec.ofNat 64 dO) (c.W + BitVec.ofNat 64 zO) (c.W + BitVec.ofNat 64 384) 16 c.R :=
    WP.block_append_iff.mpr (WP.mono (entry_wp A) fun s₁ En => WP.mono (startPre_wp L En.env)
      fun s ⟨K, _, F⟩ => ⟨s₁, En, by rw [K.pk.sp, En.sp], F⟩)
  have hb : RelCT isa (Eq2 σ₁ σ₂) (.block (entry ++ startPre)) TT := by
    refine RelCT.block_append (rel_seqR (rel_taint [.r10] hsp (agree_cons (by rw [A₁.r10, A₂.r10]) agree_nil)
      (by taint_decide)) (Runs.of_wp (entry_wp A₁)) (Runs.of_wp (entry_wp A₂)) fun τ₁ τ₂ En En' => ?_)
    exact rel_env [] En.env En'.env (by rw [En.sp, En'.sp, hsp]) agree_nil ⟨_, by taint_decide⟩
  exact rel_seqR hb (Runs.of_wp (W A₁)) (Runs.of_wp (W A₂)) fun τ₁ τ₂ ⟨_, _, h₁, F₁⟩ ⟨_, _, h₂, F₂⟩ =>
    rel_fin F₁ F₂ (by rw [h₁, h₂, hsp])

/-- `encS2v` in two runs. -/
theorem encS2v_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (A₁ : Args c σ₁) (A₂ : Args c σ₂)
    (hA₁ : Ads c σ₁.mem σ₁) (hA₂ : Ads c σ₂.mem σ₂) (hd : DescAgree c σ₁.mem σ₂.mem) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) encS2v TT := by
  unfold encS2v
  refine RelCT.assoc (rel_seqR (entryStart_rel L A₁ A₂ hsp) (Runs.of_wp (entryStart_wp A₁ hA₁))
    (Runs.of_wp (entryStart_wp A₂ hA₂)) fun τ₁ τ₂ ⟨s₁, En, I⟩ ⟨s₁', En', I'⟩ => ?_)
  have wf : WF c σ₁.mem s₁.mem := WF.of En.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  have wf' : WF c σ₂.mem s₁'.mem := WF.of En'.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  have hd₁ : DescAgree c s₁.mem s₁'.mem := fun i hi => by
    rw [wf.descW L hi (by decide), wf.descW L hi (by decide), wf'.descW L hi (by decide),
      wf'.descW L hi (by decide)]
    exact hd i hi
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [I.pk.sp, I'.pk.sp, En.sp, En'.sp, hsp]
  refine rel_seqR (s2vAds_rel L I I' hsp₁ hd₁) (Runs.of_wp (s2vAds_wp L I)) (Runs.of_wp (s2vAds_wp L I'))
    fun τ₃ τ₄ I₃ I₄ => ?_
  exact rel_env [] I₃.env I₄.env (by rw [I₃.pk.sp, I₄.pk.sp, En.sp, En'.sp, hsp]) agree_nil ⟨_, by taint_decide⟩

/-- What `encS2v` leaves. -/
theorem encS2v_runs {c : Cx} {s : State} (Ar : Args c s) (hA : Ads c s.mem s) :
    Runs encS2v s fun s' => ∃ s₁, S2vDone c s s₁ s' ∧ s'.gpr .r19 = c.D ∧ s'.gpr .r20 = BitVec.ofNat 64 c.n := by
  have h := encS2v_wp (rest := .block []) (Q := fun s' => ∃ s₁, S2vDone c s s₁ s' ∧ s'.gpr .r19 = c.D ∧
    s'.gpr .r20 = BitVec.ofNat 64 c.n) Ar hA fun s₁ s' S h19 h20 => WP.block_nil ⟨s₁, S, h19, h20⟩
  exact Runs.of_wp (WP.mono (WP.seq_iff.mp h) fun _ h => WP.block_nil_iff.mp h)

/-- `vg_aes_siv_encrypt` in two runs. -/
theorem encrypt_rel {c : Cx} {σ₁ σ₂ : State} (A₁ : Args c σ₁) (A₂ : Args c σ₂)
    (hA₁ : Ads c σ₁.mem σ₁) (hA₂ : Ads c σ₂.mem σ₂) (hd : DescAgree c σ₁.mem σ₂.mem) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) encrypt TT := by
  have L := A₁.lay
  unfold encrypt
  refine rel_seqR (encS2v_rel L A₁ A₂ hA₁ hA₂ hd hsp) (encS2v_runs A₁ hA₁) (encS2v_runs A₂ hA₂)
    fun s₄ t₄ ⟨_, S, r19, r20⟩ ⟨_, S', r19', r20'⟩ => ?_
  have E₄ := S.inv.env
  have E₄' := S'.inv.env
  have h₄ : s₄.sp = t₄.sp := by rw [S.inv.pk.sp, S'.inv.pk.sp, S.en.sp, S'.en.sp, hsp]
  refine rel_seqR (finish_rel L E₄ E₄' h₄ (L.bufD E₄.perm) (L.bufD E₄'.perm) r19 r19' r20 r20' (.inl rfl))
    (Runs.of_wp (finish_wp L E₄ (L.bufD E₄.perm) r19 r20 (out := 0) (.inl rfl)))
    (Runs.of_wp (finish_wp L E₄' (L.bufD E₄'.perm) r19' r20' (out := 0) (.inl rfl))) fun s₅ t₅ F F' => ?_
  have E₅ := E₄.of_pk F.1
  have E₅' := E₄'.of_pk F'.1
  have h₅ : s₅.sp = t₅.sp := by rw [F.1.sp, F'.1.sp, h₄]
  refine rel_seqR (ctr_rel L E₅ E₅' h₅ (src := 0) (by decide) (by decide))
    (Runs.of_wp (ctr_wp L E₅ (src := 0) (by decide) (by decide)))
    (Runs.of_wp (ctr_wp L E₅' (src := 0) (by decide) (by decide))) fun s₆ t₆ C C' => ?_
  exact rel_env [] (E₅.of_pk C.1) (E₅'.of_pk C'.1) (by rw [C.1.sp, C'.1.sp, h₅]) agree_nil ⟨_, by taint_decide⟩

/-- `vg_aes_siv_decrypt` in two runs. -/
theorem decrypt_rel {c : Cx} {σ₁ σ₂ : State} (A₁ : Args c σ₁) (A₂ : Args c σ₂)
    (hA₁ : Ads c σ₁.mem σ₁) (hA₂ : Ads c σ₂.mem σ₂) (hd : DescAgree c σ₁.mem σ₂.mem) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) decrypt TT := by
  have L := A₁.lay
  unfold decrypt
  refine rel_seqR (encS2v_rel L A₁ A₂ hA₁ hA₂ hd hsp) (encS2v_runs A₁ hA₁) (encS2v_runs A₂ hA₂)
    fun s₄ t₄ ⟨_, S, _, _⟩ ⟨_, S', _, _⟩ => ?_
  have E₄ := S.inv.env
  have E₄' := S'.inv.env
  have h₄ : s₄.sp = t₄.sp := by rw [S.inv.pk.sp, S'.inv.pk.sp, S.en.sp, S'.en.sp, hsp]
  refine rel_seqR (rel_env [] E₄ E₄' h₄ agree_nil ⟨_, by taint_decide⟩) (Runs.of_wp (sivIn_wp L E₄))
    (Runs.of_wp (sivIn_wp L E₄')) fun s₅ t₅ ⟨pk₅, _⟩ ⟨pk₅', _⟩ => ?_
  have E₅ := E₄.of_pk pk₅
  have E₅' := E₄'.of_pk pk₅'
  have h₅ : s₅.sp = t₅.sp := by rw [pk₅.sp, pk₅'.sp, h₄]
  refine rel_seqR (ctr_rel L E₅ E₅' h₅ (src := 0) (by decide) (by decide))
    (Runs.of_wp (ctr_wp L E₅ (src := 0) (by decide) (by decide)))
    (Runs.of_wp (ctr_wp L E₅' (src := 0) (by decide) (by decide))) fun s₆ t₆ C C' => ?_
  have E₆ := E₅.of_pk C.1
  have E₆' := E₅'.of_pk C'.1
  have h₆ : s₆.sp = t₆.sp := by rw [C.1.sp, C'.1.sp, h₅]
  have D (σ : State) (E : Env c σ) : WP isa (.block dataStr) σ fun s => Env c s ∧ s.sp = σ.sp ∧
      s.gpr .r19 = c.D ∧ s.gpr .r20 = BitVec.ofNat 64 c.n :=
    VG.Proof.AesCcm.PPC64LE.wp_mv fun s₁ u₁ => VG.Proof.AesCcm.PPC64LE.wp_mv fun s₂ u₂ => WP.block_nil
      ⟨E.of_pk ((PK.ofUpd u₁).trans (PK.ofUpd u₂)), by rw [u₂.sp, u₁.sp],
        by rw [u₂.other _ (by decide), u₁.gpr, E.r22], by rw [u₂.gpr, u₁.other _ (by decide), E.r23]⟩
  refine rel_seqR (rel_env [] E₆ E₆' h₆ agree_nil ⟨_, by taint_decide⟩) (Runs.of_wp (D _ E₆))
    (Runs.of_wp (D _ E₆')) fun s₇ t₇ ⟨E₇, sp₇, r19, r20⟩ ⟨E₇', sp₇', r19', r20'⟩ => ?_
  have h₇ : s₇.sp = t₇.sp := by rw [sp₇, sp₇', h₆]
  refine rel_seqR (finish_rel L E₇ E₇' h₇ (L.bufD E₇.perm) (L.bufD E₇'.perm) r19 r19' r20 r20' (.inr rfl))
    (Runs.of_wp (finish_wp L E₇ (L.bufD E₇.perm) r19 r20 (out := tO) (.inr rfl)))
    (Runs.of_wp (finish_wp L E₇' (L.bufD E₇'.perm) r19' r20' (out := tO) (.inr rfl))) fun s₈ t₈ F F' => ?_
  exact rel_env [] (E₇.of_pk F.1) (E₇'.of_pk F'.1) (by rw [F.1.sp, F'.1.sp, h₇]) agree_nil ⟨_, by taint_decide⟩

end VG.Proof.AesSiv.PPC64LE
