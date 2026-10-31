module

import VerifiedGarbage.Proof.AesCcm.PPC64LE.CallArgs
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Crypt
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.CallArgs
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Crypt
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Tag
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.AesCcm.PPC64LE
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Chunk
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
public import VerifiedGarbage.Spec.Ccm
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# AES-CCM on PPC64LE: the tag and counter mode in two runs

Untrusted: everything here is checked by Lean. `tag y`, `ctrChunk`,
`ctrTail` and `ctr`, run from two states in the same environment, leak the
same: the code between calls by the taint analysis (`rel_env`), and each
call of `vg_aes_ctr32` by its proof (`rel_ctr`). The loop over the chunks
relates two runs after the same number of blocks, which the correctness
proofs describe (`CtrInv`): the registers it branches on and the arguments
of the calls are functions of the public values.
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.Impl.AesCcm.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_li wp_and wp_lsr)
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_ite eval_zero eval_nonzero)
open VG.Impl.AesCbc.PPC64LE (mov)
open VG.Spec.Aes (bytesAt)

/-- Before the chunks: `r18`, `r19` and `r20` at the start of the data. -/
theorem ctrHeadBlk_wp {c : Cx} (L : Lay c) {nonce : List Byte} {s : State} (E : Env c s) :
    WP isa (.block [mov .r18 .r22, .lsr .d .r19 .r23 4, .li .r20 1]) s (CtrInv c nonce s 0) := by
  have hn64 := L.n_lt
  refine wp_mv fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ => WP.block_nil ?_
  exact
    { pk := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofUpd u₃))
      r18 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, E.r22]; exact (BitVec.add_zero _).symm
      r19 := by
        rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.r23,
          VG.Proof.CmacAes.Stream.PPC64LE.shr_ofNat hn64]; rfl
      r20 := u₃.gpr
      le := Nat.zero_le _
      frame := by rw [u₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _
      done := rfl
      rest := by rw [u₃.mem, u₂.mem, u₁.mem] }

/-- The length of the data's last bytes. -/
theorem lastLen_wp {c : Cx} {s : State} (E : Env c s) :
    WP isa (.block [.li .r9 15, .logic .and .r21 .r23 .r9]) s fun s' =>
      s'.gpr .r21 = s.gpr .r23 &&& BitVec.ofNat 64 15 ∧ Env c s' ∧ s'.sp = s.sp ∧
        ∀ r ∈ [Reg.r18, .r20], s'.gpr r = s.gpr r := by
  refine wp_li (by decide) fun s₁ u₁ => wp_and fun s₂ u₂ => WP.block_nil ?_
  have pk₂ : PK s s₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  refine ⟨by rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide)], E.of_pk pk₂, pk₂.sp, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> rw [u₂.other _ (by decide), u₁.other _ (by decide)]

section
variable {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
include L E₁ E₂ hsp

/-- `tag y`. -/
theorem tag_rel {y : Nat} (hy : y = 0 ∨ y = 96) : RelCT isa (Eq2 σ₁ σ₂) (tag y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ []))
      (.block ([.li .r9 0] ++ ctrAt ++ ctrArgs ++ [.addi .r6 .r14 y, .li .r7 1])) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have run : ∀ {σ : State}, Env c σ →
      Runs (.block ([.li .r9 0] ++ ctrAt ++ ctrArgs ++ [.addi .r6 .r14 y, .li .r7 1])) σ fun s' =>
        Proof.AesCtr.PPC64LE.CtrCall s' c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 y)
          (c.W + BitVec.ofNat 64 384) c.R 1 ∧ Kept c σ s' := fun E => by
    rw [List.append_assoc]
    exact Runs.block_append (Runs.kept E [.r9, .r10, .r11, .r12] (by decide +kernel)) fun s' K =>
      (Runs.of_wp (ctrArgsW_wp L K.1 (d := y) (by omega) (by omega))).mono fun _ ⟨C, K'⟩ => ⟨C, K.trans K'⟩
  unfold tag
  exact rel_seqR (rel_env [] E₁ E₂ hsp (by simp) t) (run E₁) (run E₂)
    fun τ₁ τ₂ ⟨C₁, K₁⟩ ⟨C₂, K₂⟩ => rel_ctr C₁ C₂ (by rw [K₁.2.1, K₂.2.1, hsp])

/-- `ctrTail`, from two states that agree on where the last bytes are, how
many there are, and the counter. -/
theorem ctrTail_rel (hr : ∀ r ∈ [Reg.r18, .r20, .r21], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) ctrTail TT := by
  have run : ∀ {σ : State}, Env c σ →
      Runs (.block ([mov .r9 .r20] ++ ctrAt ++ zero16 ksO ++ ctrArgs ++ [.addi .r6 .r14 ksO, .li .r7 1])) σ
        fun s' => Proof.AesCtr.PPC64LE.CtrCall s' c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 80)
          (c.W + BitVec.ofNat 64 384) c.R 1 ∧ Kept c σ s' := fun E => by
    rw [List.append_assoc]
    exact Runs.block_append (Runs.kept E [.r0, .r9, .r10, .r11, .r12] (by decide +kernel)) fun s' K =>
      (Runs.of_wp (ctrArgsW_wp L K.1 (d := 80) (by decide) (by decide))).mono fun _ ⟨C, K'⟩ => ⟨C, K.trans K'⟩
  unfold ctrTail
  refine rel_seqR (rel_env [.r20] E₁ E₂ hsp (by simpa using hr .r20 (by simp)) ⟨_, by taint_decide⟩)
    (run E₁) (run E₂) fun τ₁ τ₂ ⟨C₁, K₁⟩ ⟨C₂, K₂⟩ => ?_
  refine rel_seqR (rel_ctr C₁ C₂ (by rw [K₁.2.1, K₂.2.1, hsp])) (ctr_runs K₁.1 C₁) (ctr_runs K₂.1 C₂)
    fun ρ₁ ρ₂ G₁ G₂ => ?_
  have a₁ := K₁.trans G₁
  have a₂ := K₂.trans G₂
  refine rel_env [.r18, .r21] G₁.1 G₂.1 (by rw [a₁.2.1, a₂.2.1, hsp]) (fun r hr' => ?_) ⟨_, by taint_decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · rw [a₁.2.2 .r18 (by simp), a₂.2.2 .r18 (by simp), hr .r18 (by simp)]
  · rw [a₁.2.2 .r21 (by simp), a₂.2.2 .r21 (by simp), hr .r21 (by simp)]

/-- One chunk, from two states after the same number `b` of blocks. -/
theorem chunk_rel {b : Nat} (hb : b < c.n / 16)
    (h18₁ : σ₁.gpr .r18 = c.D + BitVec.ofNat 64 (16 * b)) (h18₂ : σ₂.gpr .r18 = c.D + BitVec.ofNat 64 (16 * b))
    (h19₁ : σ₁.gpr .r19 = BitVec.ofNat 64 (c.n / 16 - b)) (h19₂ : σ₂.gpr .r19 = BitVec.ofNat 64 (c.n / 16 - b))
    (h20₁ : σ₁.gpr .r20 = BitVec.ofNat 64 (1 + b)) (h20₂ : σ₂.gpr .r20 = BitVec.ofNat 64 (1 + b)) :
    RelCT isa (Eq2 σ₁ σ₂) ctrChunk TT := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  unfold ctrChunk
  refine RelCT.assoc (rel_seqR (rel_env [.r19, .r20] E₁ E₂ hsp (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h19₁, h19₂]
      · rw [h20₁, h20₂]) ⟨_, by taint_decide⟩)
    (Runs.of_wp (kSel_wp (b := b) h19₁ h20₁ (by omega) (by omega)))
    (Runs.of_wp (kSel_wp (b := b) h19₂ h20₂ (by omega) (by omega)))
    fun τ₁ τ₂ ⟨r21₁, pk₁, _, k₁⟩ ⟨r21₂, pk₂, _, k₂⟩ => ?_)
  obtain ⟨k, hk⟩ : ∃ k, k = min (c.n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) := ⟨_, rfl⟩
  rw [← hk] at r21₁ r21₂
  have hk1 : 1 ≤ k := by rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega
  have hkb : b + k ≤ c.n / 16 := by rw [hk]; omega
  have F₁ := E₁.of_pk pk₁
  have F₂ := E₂.of_pk pk₂
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp]
  have run : ∀ {σ τ : State}, Env c τ → σ.gpr .r18 = c.D + BitVec.ofNat 64 (16 * b) →
      (∀ r ∈ [Reg.r18, .r19, .r20], τ.gpr r = σ.gpr r) → τ.gpr .r21 = BitVec.ofNat 64 k →
      Runs (.block ([mov .r9 .r20] ++ ctrAt ++ ctrArgs ++ [mov .r6 .r18, mov .r7 .r21])) τ fun s' =>
        Proof.AesCtr.PPC64LE.CtrCall s' c.K (c.W + BitVec.ofNat 64 64) (c.D + BitVec.ofNat 64 (16 * b))
          (c.W + BitVec.ofNat 64 384) c.R k ∧ Kept c τ s' := fun F h18 kk h21 => by
    rw [List.append_assoc]
    exact Runs.block_append (Runs.kept F [.r9, .r10, .r11, .r12] (by decide +kernel)) fun s' K =>
      (Runs.of_wp (ctrArgsD_wp L K.1 hk1 hkb (by rw [K.2.2 .r18 (by simp), kk .r18 (by simp), h18])
        (by rw [K.2.2 .r21 (by simp), h21]))).mono fun _ ⟨C, K'⟩ => ⟨C, K.trans K'⟩
  refine rel_seqR (rel_env [] F₁ F₂ hsp₁ (by simp) ⟨_, by taint_decide⟩) (run F₁ h18₁ k₁ r21₁)
    (run F₂ h18₂ k₂ r21₂) fun ρ₁ ρ₂ ⟨C₁, K₁⟩ ⟨C₂, K₂⟩ => ?_
  refine rel_seqR (rel_ctr C₁ C₂ (by rw [K₁.2.1, K₂.2.1, hsp₁])) (ctr_runs K₁.1 C₁) (ctr_runs K₂.1 C₂)
    fun ω₁ ω₂ G₁ G₂ => ?_
  exact rel_env [] G₁.1 G₂.1 (by rw [G₁.2.1, G₂.2.1, K₁.2.1, K₂.2.1, hsp₁]) (by simp) ⟨_, by taint_decide⟩

end

/-- `ctr`. -/
theorem ctr_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
    {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl) (hn₂ : n₂.length = c.nl)
    (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) :
    RelCT isa (Eq2 σ₁ σ₂) ctr TT := by
  have hn64 := L.n_lt
  unfold ctr
  refine RelCT.assoc (rel_seqR ?_ (Runs.of_wp (ctrHead_wp L hn₁ E₁ hc₁)) (Runs.of_wp (ctrHead_wp L hn₂ E₂ hc₂))
    fun τ₁ τ₂ I₁ I₂ => ?_)
  · refine rel_seqR (rel_env [] E₁ E₂ hsp (by simp) ⟨_, by taint_decide⟩)
      (Runs.of_wp (ctrHeadBlk_wp L (nonce := n₁) E₁)) (Runs.of_wp (ctrHeadBlk_wp L (nonce := n₂) E₂))
      fun τ₁ τ₂ I₁ I₂ => ?_
    have e₁ := eval_zero (a := c.n / 16) (by rw [I₁.r19, Nat.sub_zero]) (by omega)
    have e₂ := eval_zero (a := c.n / 16) (by rw [I₂.r19, Nat.sub_zero]) (by omega)
    refine rel_ite e₁ e₂ (fun _ => ?_) (fun hf => ?_)
    · exact rel_env [] (E₁.of_pk I₁.pk) (E₂.of_pk I₂.pk) (by rw [I₁.pk.sp, I₂.pk.sp, hsp]) (by simp)
        ⟨_, by taint_decide⟩
    have h0 : c.n / 16 ≠ 0 := by simpa using hf
    refine (RelCT.loop (Q := TT) (fun m a b => ∃ j, m = c.n / 16 - j ∧ j < c.n / 16 ∧
        CtrInv c n₁ σ₁ j a ∧ CtrInv c n₂ σ₂ j b) (fun m => ?_) (c.n / 16 - 0)).mono
      (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨0, rfl, by omega, I₁, I₂⟩) fun _ _ h => h
    refine rel_of_eq2 fun a b ⟨j, hm, hj, J₁, J₂⟩ => ?_
    refine (rel_post (chunk_rel L (E₁.of_pk J₁.pk) (E₂.of_pk J₂.pk) (by rw [J₁.pk.sp, J₂.pk.sp, hsp]) hj
        J₁.r18 J₂.r18 J₁.r19 J₂.r19 J₁.r20 J₂.r20)
      (Runs.of_wp (chunk_wp L hn₁ E₁ hc₁ J₁ hj)) (Runs.of_wp (chunk_wp L hn₂ E₂ hc₂ J₂ hj))).mono
      (fun _ _ h => h) fun a' b' ⟨⟨k, hk, hk1, hkb, K₁⟩, ⟨k', hk', _, _, K₂⟩⟩ => ?_
    have e : k = k' := by rw [hk, hk']
    subst e
    have ev₁ := eval_nonzero (r := .r19) (a := c.n / 16 - (j + k)) K₁.r19 (by omega)
    have ev₂ := eval_nonzero (r := .r19) (a := c.n / 16 - (j + k)) K₂.r19 (by omega)
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ⟨c.n / 16 - (j + k), ?_, j + k, rfl, ?_, K₁, K₂⟩⟩
    · rw [ev₁] at ht; simp at ht; omega
    · rw [ev₁] at ht; simp at ht; omega
  · have F₁ := E₁.of_pk I₁.pk
    have F₂ := E₂.of_pk I₂.pk
    have hsp₁ : τ₁.sp = τ₂.sp := by rw [I₁.pk.sp, I₂.pk.sp, hsp]
    refine rel_seqR (rel_env [] F₁ F₂ hsp₁ (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (lastLen_wp F₁))
      (Runs.of_wp (lastLen_wp F₂)) fun ρ₁ ρ₂ ⟨r21₁, G₁, sp₁, k₁⟩ ⟨r21₂, G₂, sp₂, k₂⟩ => ?_
    have hsp₂ : ρ₁.sp = ρ₂.sp := by rw [sp₁, sp₂, hsp₁]
    have q21 : ρ₁.gpr .r21 = ρ₂.gpr .r21 := by rw [r21₁, r21₂, F₁.r23, F₂.r23]
    refine rel_iteZ q21 (rel_env [] G₁ G₂ hsp₂ (by simp) ⟨_, by taint_decide⟩) ?_
    refine ctrTail_rel L G₁ G₂ hsp₂ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [k₁ .r18 (by simp), k₂ .r18 (by simp), I₁.r18, I₂.r18]
    · rw [k₁ .r20 (by simp), k₂ .r20 (by simp), I₁.r20, I₂.r20]
    · exact q21

end VG.Proof.AesCcm.PPC64LE
