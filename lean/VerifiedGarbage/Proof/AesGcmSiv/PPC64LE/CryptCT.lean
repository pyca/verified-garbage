module

import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Rel
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Crypt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Rel
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Crypt
import VerifiedGarbage.Proof.AesCcm.PPC64LE.CallArgs
meta import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.CallArgs
public import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Env
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
public import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# AES-GCM-SIV on PPC64LE: the tag and counter mode in two runs

Untrusted: everything here is checked by Lean. `tag o` and `crypt`, run from
two states in the same environment, leak the same: the code between calls
by the taint analysis (`rel_env`), from the pointer `r23` and the count
`r24`, which are public in both runs, and each call of `vg_aes_ctr32` by its
proof (`rel_ctr`). The loop of blocks relates two runs after the same number
of blocks, which the correctness proofs describe (`BlocksPost`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.Impl.AesGcmSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_ite eval_zero eval_nonzero)
open VG.Proof.AesCcm.PPC64LE (Runs Runs.of_wp Runs.mono Runs.and rel_seqR rel_of_eq2 rel_post)
open VG.Spec.Aes (bytesAt)

/-- `tag o`. -/
theorem tag_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
    {o : Nat} (ho : o = 0 ∨ o = 240) : RelCT isa (Eq2 σ₁ σ₂) (tag o) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ []))
      (.block (copy16 cbO ccO ++ zero16 o ++ ctrArgs ++ ([.addi .r6 .r14 o, .li .r7 1] : List Instr))) h).isSome
        = true := by
    rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold tag
  exact rel_seqR (rel_env [] E₁ E₂ hsp (by simp) t) (Runs.of_wp (tagArgs_wp L E₁ ho))
    (Runs.of_wp (tagArgs_wp L E₂ ho)) fun τ₁ τ₂ ⟨pk₁, _, C₁, _⟩ ⟨pk₂, _, C₂, _⟩ =>
      rel_ctr C₁ C₂ (by rw [pk₁.sp, pk₂.sp, hsp])

/-- One block, from two runs after the same number `j` of blocks. -/
theorem cryptBlock_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂)
    (hsp : σ₁.sp = σ₂.sp) {j : Nat} (hj : 16 * (j + 1) ≤ c.n)
    (h23₁ : σ₁.gpr .r23 = c.D + BitVec.ofNat 64 (16 * j)) (h23₂ : σ₂.gpr .r23 = c.D + BitVec.ofNat 64 (16 * j))
    (h24₁ : σ₁.gpr .r24 = BitVec.ofNat 64 (c.n - 16 * j)) (h24₂ : σ₂.gpr .r24 = BitVec.ofNat 64 (c.n - 16 * j)) :
    RelCT isa (Eq2 σ₁ σ₂) cryptBlock TT := by
  unfold cryptBlock
  refine rel_seqR (rel_env [.r23] E₁ E₂ hsp (by simp [h23₁, h23₂]) ⟨_, by taint_decide⟩)
    (Runs.of_wp (blkArgs_wp L E₁ hj h23₁)) (Runs.of_wp (blkArgs_wp L E₂ hj h23₂))
    fun τ₁ τ₂ ⟨pk₁, _, C₁, r23₁, r24₁⟩ ⟨pk₂, _, C₂, r23₂, r24₂⟩ => ?_
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp]
  refine rel_seqR (rel_ctr C₁ C₂ hsp₁) (ctr_runs (E₁.of_pk pk₁) C₁) (ctr_runs (E₂.of_pk pk₂) C₂)
    fun ω₁ ω₂ G₁ G₂ => ?_
  refine rel_env [.r23, .r24] G₁.1 G₂.1 (by rw [G₁.2.1, G₂.2.1, hsp₁]) (fun r hr => ?_) ⟨_, by taint_decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [G₁.2.2 .r23 (by simp), G₂.2.2 .r23 (by simp), r23₁, r23₂, h23₁, h23₂]
  · rw [G₁.2.2 .r24 (by simp), G₂.2.2 .r24 (by simp), r24₁, r24₂, h24₁, h24₂]

/-- `crypt`. -/
theorem crypt_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) crypt TT := by
  have hn := L.n_lt
  unfold crypt
  refine rel_seqR (rel_env [] E₁ E₂ hsp (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (cryptHead_wp L E₁))
    (Runs.of_wp (cryptHead_wp L E₂)) fun τ₁ τ₂ H₁ H₂ => ?_
  have F₁ := E₁.of_pk H₁.pk
  have F₂ := E₂.of_pk H₂.pk
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [H₁.pk.sp, H₂.pk.sp, hsp]
  have hxl₁ : (bytesAt σ₁.mem c.D c.n).length = c.n := Proof.Cmac.bytesAt_length _ _ _
  have hxl₂ : (bytesAt σ₂.mem c.D c.n).length = c.n := Proof.Cmac.bytesAt_length _ _ _
  -- What the whole blocks leave in each run, from the correctness proofs.
  have mid : ∀ {σ τ : State}, Env c σ → HeadPost c σ τ → Runs (.ite (.zero .d .r11) (.block [])
      (.loop cryptBlock (.nonzero .d .r11))) τ fun ρ => PK τ ρ ∧ ρ.gpr .r23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)) ∧
        ρ.gpr .r24 = BitVec.ofNat 64 (c.n - 16 * (c.n / 16)) := fun {σ τ} E H => by
    refine Runs.of_wp (WP.ite (decide (c.n / 16 = 0)) (eval_zero H.r11 (by omega)) (fun ht => ?_) (fun hf => ?_))
    · have h0 : c.n / 16 = 0 := by simpa using ht
      exact WP.block_nil ⟨PK.refl _, by rw [H.r23, h0, Nat.mul_zero, BitVec.add_zero],
        by rw [H.r24, h0, Nat.mul_zero, Nat.sub_zero]⟩
    · have h0 : c.n / 16 ≠ 0 := by simpa using hf
      exact WP.mono (blocks_wp L (E.of_pk H.pk) (Proof.Cmac.bytesAt_length σ.mem c.D c.n) (by omega) H.r23 H.r24
        H.ctr H.data H.ciph) fun ρ B => ⟨B.pk, B.r23, B.r24⟩
  refine rel_seqR ?_ (mid E₁ H₁) (mid E₂ H₂) fun ρ₁ ρ₂ ⟨pk₁, r23₁, r24₁⟩ ⟨pk₂, r23₂, r24₂⟩ => ?_
  · refine rel_ite (eval_zero H₁.r11 (by omega)) (eval_zero H₂.r11 (by omega)) (fun _ => ?_) (fun hf => ?_)
    · exact rel_env [] F₁ F₂ hsp₁ (by simp) ⟨_, by taint_decide⟩
    have h0 : c.n / 16 ≠ 0 := by simpa using hf
    refine (RelCT.loop (Q := TT) (fun k (a b : State) => ∃ j, k = c.n / 16 - j ∧ j < c.n / 16 ∧
        BlocksPost c (Spec.GcmSiv.ctxCiph σ₁.mem (c.W + BitVec.ofNat 64 256) c.R)
          (Spec.GcmSiv.initialCounter (bytesAt σ₁.mem c.W 16)) (bytesAt σ₁.mem c.D c.n) j τ₁ a ∧
        BlocksPost c (Spec.GcmSiv.ctxCiph σ₂.mem (c.W + BitVec.ofNat 64 256) c.R)
          (Spec.GcmSiv.initialCounter (bytesAt σ₂.mem c.W 16)) (bytesAt σ₂.mem c.D c.n) j τ₂ b)
        (fun k => ?_) (c.n / 16 - 0)).mono
      (fun a b hab => by
        obtain ⟨rfl, rfl⟩ := hab
        exact ⟨0, rfl, by omega,
          ⟨PK.refl _, by rw [H₁.r23, Nat.mul_zero, BitVec.add_zero], by rw [H₁.r24, Nat.mul_zero, Nat.sub_zero],
            H₁.ctr, by rw [H₁.data, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩,
          ⟨PK.refl _, by rw [H₂.r23, Nat.mul_zero, BitVec.add_zero], by rw [H₂.r24, Nat.mul_zero, Nat.sub_zero],
            H₂.ctr, by rw [H₂.data, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩) fun _ _ h => h
    refine rel_of_eq2 fun a b ⟨j, hk, hj, P₁, P₂⟩ => ?_
    have hc₁ : Spec.GcmSiv.ctxCiph a.mem (c.W + BitVec.ofNat 64 256) c.R =
        Spec.GcmSiv.ctxCiph σ₁.mem (c.W + BitVec.ofNat 64 256) c.R := by rw [ciph_cryR L P₁.frame, H₁.ciph]
    have hc₂ : Spec.GcmSiv.ctxCiph b.mem (c.W + BitVec.ofNat 64 256) c.R =
        Spec.GcmSiv.ctxCiph σ₂.mem (c.W + BitVec.ofNat 64 256) c.R := by rw [ciph_cryR L P₂.frame, H₂.ciph]
    have G₁ := F₁.of_pk P₁.pk
    have G₂ := F₂.of_pk P₂.pk
    refine (rel_post (cryptBlock_rel L G₁ G₂ (by rw [P₁.pk.sp, P₂.pk.sp, hsp₁]) (j := j) (by omega)
        P₁.r23 P₂.r23 P₁.r24 P₂.r24)
      (Runs.of_wp (cryptBlock_wp L G₁ hxl₁ (j := j) (by omega) P₁.r23 P₁.r24 P₁.ctr P₁.data hc₁))
      (Runs.of_wp (cryptBlock_wp L G₂ hxl₂ (j := j) (by omega) P₂.r23 P₂.r24 P₂.ctr P₂.data hc₂))).mono
      (fun _ _ h => h) fun a' b' ⟨Q₁, Q₂⟩ => ?_
    have ev₁ := eval_nonzero Q₁.r11 (by omega)
    have ev₂ := eval_nonzero Q₂.r11 (by omega)
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ⟨c.n / 16 - (j + 1), ?_, j + 1, rfl, ?_,
      ⟨P₁.pk.trans Q₁.pk, Q₁.r23, Q₁.r24, Q₁.ctr, Q₁.data, P₁.frame.trans Q₁.frame⟩,
      ⟨P₂.pk.trans Q₂.pk, Q₂.r23, Q₂.r24, Q₂.ctr, Q₂.data, P₂.frame.trans Q₂.frame⟩⟩⟩
    · rw [ev₁] at ht; simp at ht; omega
    · rw [ev₁] at ht; simp at ht; omega
  · have G₁ := F₁.of_pk pk₁
    have G₂ := F₂.of_pk pk₂
    have hsp₂ : ρ₁.sp = ρ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp₁]
    have q24₁ : ρ₁.gpr .r24 = BitVec.ofNat 64 (c.n % 16) := by rw [r24₁]; congr 1; omega
    have q24₂ : ρ₂.gpr .r24 = BitVec.ofNat 64 (c.n % 16) := by rw [r24₂]; congr 1; omega
    refine rel_ite (eval_zero q24₁ (by omega)) (eval_zero q24₂ (by omega)) (fun _ => ?_) (fun _ => ?_)
    · exact rel_env [] G₁ G₂ hsp₂ (by simp) ⟨_, by taint_decide⟩
    unfold cryptTail
    refine rel_seqR (tag_rel L G₁ G₂ hsp₂ (o := 240) (by decide)) (Runs.of_wp (tag_wp L G₁ (o := 240) (by decide)))
      (Runs.of_wp (tag_wp L G₂ (o := 240) (by decide))) fun ω₁ ω₂ T₁ T₂ => ?_
    refine rel_env [.r23, .r24] (G₁.of_pk T₁.pk) (G₂.of_pk T₂.pk) (by rw [T₁.pk.sp, T₂.pk.sp, hsp₂])
      (fun r hr => ?_) ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [T₁.r23, T₂.r23, r23₁, r23₂]
    · rw [T₁.r24, T₂.r24, q24₁, q24₂]

end VG.Proof.AesGcmSiv.PPC64LE
