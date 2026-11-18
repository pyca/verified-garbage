module

public import VerifiedGarbage.Proof.AesCcm.Scratch
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Seal
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Open
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesCcm.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Entry
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Fn
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Fn
meta import VerifiedGarbage.Proof.AesCcm.BytesAt
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Open
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Ctrs
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Crypt
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
public import VerifiedGarbage.Spec.TripleDes
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Header
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Crypt
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Ctrs
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Mac
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Seal
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Mac
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.CallArgs
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.CallArgs
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Header
meta import VerifiedGarbage.Impl.AesCcm.PPC64LE
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Env
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Spec.Ccm
meta import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
meta import VerifiedGarbage.Spec.Ccm

/-! ### `AesCcm.PPC64LE.TopCT`, which only this module used -/

section

/-! ### `AesCcm.PPC64LE.CtrCT`, which only this module used -/

section

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
      (Runs.of_wp (ctrArgsW_wp L K.1 (d := y) (by omega_using [hy]) (by omega_using [hy]))).mono fun _ ⟨C, K'⟩ => ⟨C, K.trans K'⟩
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
    (Runs.of_wp (kSel_wp (b := b) h19₁ h20₁ (by omega_using [hn64]) (by omega_using [hb, hn64])))
    (Runs.of_wp (kSel_wp (b := b) h19₂ h20₂ (by omega_using [hn64]) (by omega_using [hb, hn64])))
    fun τ₁ τ₂ ⟨r21₁, pk₁, _, k₁⟩ ⟨r21₂, pk₂, _, k₂⟩ => ?_)
  obtain ⟨k, hk⟩ : ∃ k, k = min (c.n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) := ⟨_, rfl⟩
  rw [← hk] at r21₁ r21₂
  have hk1 : 1 ≤ k := by rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega_using [hb]
  have hkb : b + k ≤ c.n / 16 := by rw [hk]; omega_using [hb]
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
    have e₁ := eval_zero (a := c.n / 16) (by rw [I₁.r19, Nat.sub_zero]) (by omega_using [hn64])
    have e₂ := eval_zero (a := c.n / 16) (by rw [I₂.r19, Nat.sub_zero]) (by omega_using [hn64])
    refine rel_ite e₁ e₂ (fun _ => ?_) (fun hf => ?_)
    · exact rel_env [] (E₁.of_pk I₁.pk) (E₂.of_pk I₂.pk) (by rw [I₁.pk.sp, I₂.pk.sp, hsp]) (by simp)
        ⟨_, by taint_decide⟩
    have h0 : c.n / 16 ≠ 0 := by simpa using hf
    refine (RelCT.loop (Q := TT) (fun m a b => ∃ j, m = c.n / 16 - j ∧ j < c.n / 16 ∧
        CtrInv c n₁ σ₁ j a ∧ CtrInv c n₂ σ₂ j b) (fun m => ?_) (c.n / 16 - 0)).mono
      (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨0, rfl, by omega_using [h0], I₁, I₂⟩) fun _ _ h => h
    refine rel_of_eq2 fun a b ⟨j, hm, hj, J₁, J₂⟩ => ?_
    refine (rel_post (chunk_rel L (E₁.of_pk J₁.pk) (E₂.of_pk J₂.pk) (by rw [J₁.pk.sp, J₂.pk.sp, hsp]) hj
        J₁.r18 J₂.r18 J₁.r19 J₂.r19 J₁.r20 J₂.r20)
      (Runs.of_wp (chunk_wp L hn₁ E₁ hc₁ J₁ hj)) (Runs.of_wp (chunk_wp L hn₂ E₂ hc₂ J₂ hj))).mono
      (fun _ _ h => h) fun a' b' ⟨⟨k, hk, hk1, hkb, K₁⟩, ⟨k', hk', _, _, K₂⟩⟩ => ?_
    have e : k = k' := by rw [hk, hk']
    subst e
    have ev₁ := eval_nonzero (r := .r19) (a := c.n / 16 - (j + k)) K₁.r19 (by omega_using [hn64])
    have ev₂ := eval_nonzero (r := .r19) (a := c.n / 16 - (j + k)) K₂.r19 (by omega_using [hn64])
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ⟨c.n / 16 - (j + k), ?_, j + k, rfl, ?_, K₁, K₂⟩⟩
    · rw [ev₁] at ht; simp at ht; omega_using [hm, hj, hk]
    · rw [ev₁] at ht; simp at ht; omega_using [ht]
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

end

end

/-! ### `AesCcm.PPC64LE.MacCT`, which only this module used -/

section

/-!
# AES-CCM on PPC64LE: the CBC-MAC in two runs

Untrusted: everything here is checked by Lean. Each piece of `mac y`, run
from two states in the same environment, leaks the same: the code between
calls by the taint analysis (`rel_env`), from the environment's registers
and those on which the two runs agree (the pointer and the length of the
string being absorbed, in `r18` and `r19`, which the correctness proofs pin),
and each call of `vg_cmac_aes_update` by its proof (`rel_upd`), from the
arguments `CallArgs.lean` gives it.
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.Impl.AesCcm.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_ld wp_li wp_and)
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_ite eval_zero)
open VG.Impl.AesCbc.PPC64LE (mov)

/-- Code without calls that writes none of the environment's registers. -/
theorem Runs.env {c : Cx} {code : Prog isa} {s : State} (E : Env c s) (rs : List Reg)
    (hc : writesOnly rs code = true) (hd : ∀ r ∈ keepRegs, r ∉ rs := by decide)
    (hn : code.noCalls = true := by decide +kernel) : Runs code s fun s' => Env c s' ∧ s'.sp = s.sp :=
  (Runs.keep rs hc hn).mono fun _ ⟨k, sp⟩ => ⟨E.of_pk (PK.ofKeep k sp hd), sp⟩

/-! ## What the pieces set -/

/-- The pointer to and the length of the associated data, from their slots. -/
theorem aadLd_wp {c : Cx} {s : State} (E : Env c s) (S : Slots c s.mem) :
    WP isa (.block [.load .d .r18 .r14 aadO, .load .d .r19 .r14 alenO]) s fun s' =>
      s'.gpr .r18 = c.A ∧ s'.gpr .r19 = BitVec.ofNat 64 c.al ∧ Env c s' ∧ s'.sp = s.sp := by
  refine wp_ld (a := c.W + BitVec.ofNat 64 216) (by decide) (by decide) (by rw [E.r14]; rfl)
    (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 224) (by decide) (by decide) (by rw [u₁.other _ (by decide), E.r14]; rfl)
    (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₂ u₂ => WP.block_nil ?_
  have pk₂ : PK s s₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  exact ⟨by rw [u₂.other _ (by decide), u₁.gpr, S.aad], by rw [u₂.gpr, u₁.mem, S.alen], E.of_pk pk₂, pk₂.sp⟩

/-- The pointer to and the length of the data. -/
theorem dataArgs_wp {c : Cx} {s : State} (E : Env c s) :
    WP isa (.block [mov .r18 .r22, mov .r19 .r23]) s fun s' =>
      s'.gpr .r18 = c.D ∧ s'.gpr .r19 = BitVec.ofNat 64 c.n ∧ Env c s' ∧ s'.sp = s.sp := by
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => WP.block_nil ?_
  have pk₂ : PK s s₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  exact ⟨by rw [u₂.other _ (by decide), u₁.gpr, E.r22], by rw [u₂.gpr, u₁.other _ (by decide), E.r23],
    E.of_pk pk₂, pk₂.sp⟩

/-- The length's last 4 bits. -/
theorem mask15_wp {c : Cx} {s : State} (E : Env c s) :
    WP isa (.block [.li .r9 15, .logic .and .r21 .r19 .r9]) s fun s' =>
      s'.gpr .r21 = s.gpr .r19 &&& BitVec.ofNat 64 15 ∧ Env c s' ∧ s'.sp = s.sp ∧
        ∀ r ∈ [Reg.r18, .r19], s'.gpr r = s.gpr r := by
  refine wp_li (by decide) fun s₁ u₁ => wp_and fun s₂ u₂ => WP.block_nil ?_
  have pk₂ : PK s s₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  refine ⟨by rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide)], E.of_pk pk₂, pk₂.sp, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> rw [u₂.other _ (by decide), u₁.other _ (by decide)]

/-! ## What every run of a piece keeps -/

theorem updBlock_runs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96) :
    Runs (updBlock y) s (Kept c s) := by
  unfold updBlock
  exact Runs.seq (Runs.of_wp (updArgs1_wp L E hy)) fun _ ⟨U, K⟩ => (upd_runs K.1 U).mono fun _ K' => K.trans K'

theorem b0_runs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96) :
    Runs (b0 y) s (Kept c s) := by
  unfold b0
  refine Runs.seq (Runs.kept E [.r9, .r10, .r11] (by decide +kernel)) fun _ K => ?_
  refine Runs.seq (Runs.kept K.1 [.r0, .r9, .r10, .r11, .r12] (by rcases hy with rfl | rfl <;> decide +kernel)
    (hn := by rcases hy with rfl | rfl <;> decide +kernel)) fun _ K' => ?_
  exact (updBlock_runs L K'.1 hy).mono fun _ K'' => K.trans (K'.trans K'')

/-! ## Two runs -/

section
variable {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
  {y : Nat} (hy : y = 0 ∨ y = 96)
include L E₁ E₂ hsp hy

/-- `updBlock y`. -/
theorem updBlock_rel : RelCT isa (Eq2 σ₁ σ₂) (updBlock y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ []))
      (.block (updArgs y ++ [.addi .r6 .r14 bO, .li .r7 1])) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  exact rel_seqR (rel_env [] E₁ E₂ hsp (by simp) t) (Runs.of_wp (updArgs1_wp L E₁ hy))
    (Runs.of_wp (updArgs1_wp L E₂ hy)) fun τ₁ τ₂ ⟨U₁, K₁⟩ ⟨U₂, K₂⟩ => rel_upd U₁ U₂ (by rw [K₁.2.1, K₂.2.1, hsp])

/-- `absTail y`, from two states that agree on the string and the length of
its tail. -/
theorem absTail_rel (hr : ∀ r ∈ [Reg.r18, .r19, .r21], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (absTail y) TT := by
  unfold absTail
  exact RelCT.assoc (rel_seqR (rel_env [.r18, .r19, .r21] E₁ E₂ hsp hr ⟨_, by taint_decide⟩)
    (Runs.env E₁ [.r0, .r3, .r4, .r5, .r6, .r9, .r10] (by decide +kernel))
    (Runs.env E₂ [.r0, .r3, .r4, .r5, .r6, .r9, .r10] (by decide +kernel))
    fun τ₁ τ₂ F₁ F₂ => updBlock_rel L F₁.1 F₂.1 (by rw [F₁.2, F₂.2, hsp]) hy)

/-- `absorbPad y`, for the `len` bytes at `P`. -/
theorem absorbPad_rel {P : Addr} {len : Nat} (hP₁ : Buf c σ₁ P len) (hP₂ : Buf c σ₂ P len)
    (h18₁ : σ₁.gpr .r18 = P) (h18₂ : σ₂.gpr .r18 = P) (h19₁ : σ₁.gpr .r19 = BitVec.ofNat 64 len)
    (h19₂ : σ₂.gpr .r19 = BitVec.ofNat 64 len) :
    RelCT isa (Eq2 σ₁ σ₂) (absorbPad y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.r18, .r19]))
      (.block (updArgs y ++ [mov .r6 .r18, .lsr .d .r7 .r19 4])) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold absorbPad
  refine rel_seqR (rel_env [.r18, .r19] E₁ E₂ hsp (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h18₁, h18₂]
      · rw [h19₁, h19₂]) t)
    (Runs.of_wp (absArgs_wp L E₁ hy hP₁ h18₁ h19₁)) (Runs.of_wp (absArgs_wp L E₂ hy hP₂ h18₂ h19₂))
    fun τ₁ τ₂ ⟨U₁, K₁⟩ ⟨U₂, K₂⟩ => ?_
  refine rel_seqR (rel_upd U₁ U₂ (by rw [K₁.2.1, K₂.2.1, hsp])) (upd_runs K₁.1 U₁) (upd_runs K₂.1 U₂)
    fun ρ₁ ρ₂ G₁ G₂ => ?_
  have a₁ := K₁.trans G₁
  have a₂ := K₂.trans G₂
  have q : ∀ r ∈ [Reg.r18, .r19], ρ₁.gpr r = ρ₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [a₁.2.2 .r18 (by simp), a₂.2.2 .r18 (by simp), h18₁, h18₂]
    · rw [a₁.2.2 .r19 (by simp), a₂.2.2 .r19 (by simp), h19₁, h19₂]
  refine rel_seqR (rel_env [.r18, .r19] G₁.1 G₂.1 (by rw [a₁.2.1, a₂.2.1, hsp]) q ⟨_, by taint_decide⟩)
    (Runs.of_wp (mask15_wp G₁.1)) (Runs.of_wp (mask15_wp G₂.1)) fun κ₁ κ₂ ⟨r21₁, F₁, sp₁, k₁⟩ ⟨r21₂, F₂, sp₂, k₂⟩ => ?_
  have hsp' : κ₁.sp = κ₂.sp := by rw [sp₁, sp₂, a₁.2.1, a₂.2.1, hsp]
  have q21 : κ₁.gpr .r21 = κ₂.gpr .r21 := by rw [r21₁, r21₂, q .r19 (by simp)]
  refine rel_iteZ q21 (rel_env [] F₁ F₂ hsp' (by simp) ⟨_, by taint_decide⟩) ?_
  refine absTail_rel L F₁ F₂ hsp' hy fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [k₁ .r18 (by simp), k₂ .r18 (by simp), q .r18 (by simp)]
  · rw [k₁ .r19 (by simp), k₂ .r19 (by simp), q .r19 (by simp)]
  · exact q21

/-- `aadHead y`, from two states that agree on the associated data. -/
theorem aadHead_rel (hr : ∀ r ∈ [Reg.r18, .r19], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (aadHead y) TT := by
  unfold aadHead
  exact RelCT.assoc (RelCT.assoc (RelCT.assoc (RelCT.assoc (rel_seqR
    (rel_env [.r18, .r19] E₁ E₂ hsp hr ⟨_, by taint_decide⟩)
    (Runs.env E₁ [.r0, .r3, .r4, .r5, .r6, .r9, .r10, .r11, .r18, .r19, .r20, .r21] (by decide +kernel))
    (Runs.env E₂ [.r0, .r3, .r4, .r5, .r6, .r9, .r10, .r11, .r18, .r19, .r20, .r21] (by decide +kernel))
    fun τ₁ τ₂ F₁ F₂ => updBlock_rel L F₁.1 F₂.1 (by rw [F₁.2, F₂.2, hsp]) hy))))

/-- The associated data, if there is any. -/
theorem aadPart_rel (h18₁ : σ₁.gpr .r18 = c.A) (h18₂ : σ₂.gpr .r18 = c.A)
    (h19₁ : σ₁.gpr .r19 = BitVec.ofNat 64 c.al) (h19₂ : σ₂.gpr .r19 = BitVec.ofNat 64 c.al) :
    RelCT isa (Eq2 σ₁ σ₂) (.ite (.zero .d .r19) (.block []) (.seq (aadHead y) (absorbPad y))) TT := by
  have ha := L.al_lt
  refine rel_ite (eval_zero h19₁ ha) (eval_zero h19₂ ha) (fun _ => ?_) (fun hf => ?_)
  · exact rel_env [] E₁ E₂ hsp (by simp) ⟨_, by taint_decide⟩
  have h0 : c.al ≠ 0 := by simpa using hf
  have hA₁ := L.bufA E₁.perm
  have hA₂ := L.bufA E₂.perm
  refine rel_seqR (aadHead_rel L E₁ E₂ hsp hy fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h18₁, h18₂]
      · rw [h19₁, h19₂])
    (Runs.of_wp (aadHead_wp L E₁ hy hA₁ h18₁ h19₁ (by omega_using [h0])))
    (Runs.of_wp (aadHead_wp L E₂ hy hA₂ h18₂ h19₂ (by omega_using [h0]))) fun τ₁ τ₂ A₁ A₂ => ?_
  have hn1 : Proof.AesCcm.headLen c.al ≤ c.al := by unfold Proof.AesCcm.headLen; omega_using []
  exact absorbPad_rel L (E₁.of_pk A₁.abs.pk) (E₂.of_pk A₂.abs.pk) (by rw [A₁.abs.pk.sp, A₂.abs.pk.sp, hsp]) hy
    ((hA₁.drop hn1).of_eq A₁.abs.pk.rd A₁.abs.pk.wr) ((hA₂.drop hn1).of_eq A₂.abs.pk.rd A₂.abs.pk.wr)
    A₁.r18 A₂.r18 A₁.r19 A₂.r19

/-- `b0 y`, from two states that agree on the length of the associated data. -/
theorem b0_rel (h19 : σ₁.gpr .r19 = σ₂.gpr .r19) : RelCT isa (Eq2 σ₁ σ₂) (b0 y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.r19])) (.seq flagsSeg (.block (b0Seg y))) h).isSome =
      true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold b0
  exact RelCT.assoc (rel_seqR (rel_env [.r19] E₁ E₂ hsp (by simpa using h19) t)
    (Runs.env E₁ [.r0, .r9, .r10, .r11, .r12] (by rcases hy with rfl | rfl <;> decide +kernel)
      (hn := by rcases hy with rfl | rfl <;> decide +kernel))
    (Runs.env E₂ [.r0, .r9, .r10, .r11, .r12] (by rcases hy with rfl | rfl <;> decide +kernel)
      (hn := by rcases hy with rfl | rfl <;> decide +kernel))
    fun τ₁ τ₂ F₁ F₂ => updBlock_rel L F₁.1 F₂.1 (by rw [F₁.2, F₂.2, hsp]) hy)

/-- `mac y`. -/
theorem mac_rel (S₁ : Slots c σ₁.mem) (S₂ : Slots c σ₂.mem) : RelCT isa (Eq2 σ₁ σ₂) (mac y) TT := by
  unfold mac
  refine rel_seqR (rel_env [] E₁ E₂ hsp (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (aadLd_wp E₁ S₁))
    (Runs.of_wp (aadLd_wp E₂ S₂)) fun τ₁ τ₂ ⟨x18₁, x19₁, F₁, sp₁⟩ ⟨x18₂, x19₂, F₂, sp₂⟩ => ?_
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [sp₁, sp₂, hsp]
  refine rel_seqR (b0_rel L F₁ F₂ hsp₁ hy (by rw [x19₁, x19₂])) (b0_runs L F₁ hy) (b0_runs L F₂ hy)
    fun κ₁ κ₂ B₁ B₂ => ?_
  have hsp₂ : κ₁.sp = κ₂.sp := by rw [B₁.2.1, B₂.2.1, hsp₁]
  have y18₁ : κ₁.gpr .r18 = c.A := by rw [B₁.2.2 .r18 (by simp), x18₁]
  have y18₂ : κ₂.gpr .r18 = c.A := by rw [B₂.2.2 .r18 (by simp), x18₂]
  have y19₁ : κ₁.gpr .r19 = BitVec.ofNat 64 c.al := by rw [B₁.2.2 .r19 (by simp), x19₁]
  have y19₂ : κ₂.gpr .r19 = BitVec.ofNat 64 c.al := by rw [B₂.2.2 .r19 (by simp), x19₂]
  refine rel_seqR (aadPart_rel L B₁.1 B₂.1 hsp₂ hy y18₁ y18₂ y19₁ y19₂)
    (Runs.of_wp (aad_wp L B₁.1 hy y18₁ y19₁)) (Runs.of_wp (aad_wp L B₂.1 hy y18₂ y19₂)) fun ρ₁ ρ₂ P₁ P₂ => ?_
  have G₁ := B₁.1.of_pk P₁.pk
  have G₂ := B₂.1.of_pk P₂.pk
  have hsp₃ : ρ₁.sp = ρ₂.sp := by rw [P₁.pk.sp, P₂.pk.sp, hsp₂]
  refine rel_seqR (rel_env [] G₁ G₂ hsp₃ (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (dataArgs_wp G₁))
    (Runs.of_wp (dataArgs_wp G₂)) fun ω₁ ω₂ ⟨z18₁, z19₁, H₁, sp₁'⟩ ⟨z18₂, z19₂, H₂, sp₂'⟩ => ?_
  exact absorbPad_rel L H₁ H₂ (by rw [sp₁', sp₂', hsp₃]) hy (L.bufD H₁.perm) (L.bufD H₂.perm) z18₁ z18₂ z19₁ z19₂

end

end VG.Proof.AesCcm.PPC64LE

end

end

/-!
# AES-CCM on PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments have the same public values (`args_two`). The entry loads `work`
from the stack, which the taint analysis takes as secret (it reads memory):
the block is split after the load, and the rest runs from `r11` and `r12`,
which hold `work` and the stack pointer in both runs (`entry_rel`). So do the
loads of the tag's address from its slot in `W`, before `tagOut` and `cmp`.
The other pieces are related by `MacCT.lean` and `CtrCT.lean` (`seal_rel`,
`open_rel`). `open` compares the tags and masks the plaintext without a
branch: whether it succeeds is not leaked.
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.Impl.AesCcm.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_ld)
open VG.Proof.ChaCha20Poly1305.PPC64LE.Gather (wp_addSp)
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_taint ct_of in_off)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt)

/-- Two runs with the same public arguments: both from the public values of
the first. -/
theorem args_two {σ₁ σ₂ : State} (A₂ : Args (cxOf σ₂) (σ₂.gpr .r5) σ₂)
    (hq : onePub σ₁ σ₂) : Args (cxOf σ₁) (σ₁.gpr .r5) σ₂ := by
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩ := hq
  obtain hcx : cxOf σ₂ = cxOf σ₁ := by
    simp only [cxOf, q3, q4, q6, q7, q8, q9, q10, qa 0 (by decide), qa 1 (by decide), qa 2 (by decide)]
  rw [hcx, ← q5] at A₂
  exact A₂

/-- `work` and the stack pointer. -/
theorem entryLd_wp {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) :
    WP isa (.block [.addSp .r12 0, .load .d .r11 .r12 112]) s fun s' =>
      s'.gpr .r11 = c.W ∧ s'.gpr .r12 = s.sp ∧ s'.sp = s.sp := by
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  obtain r12₁ : s₁.gpr .r12 = s.sp := by rw [u₁.gpr, BitVec.add_zero]
  refine wp_ld (a := stackArgAddr s 2) (by decide) (by decide) (by rw [r12₁]; rfl)
    (by rw [u₁.rd, u₁.wr, stackArgAddr_succ]; exact in_off Ar.argsC (by omega_using []) (by decide))
    fun s₂ u₂ => WP.block_nil ⟨by rw [u₂.gpr, u₁.mem, ← Ar.w]; rfl, by rw [u₂.other _ (by decide), r12₁],
      by rw [u₂.sp, u₁.sp]⟩

/-- The entry in two runs. -/
theorem entry_rel {c : Cx} {N : Addr} {σ₁ σ₂ : State} (A₁ : Args c N σ₁) (A₂ : Args c N σ₂)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  have e : entry = [.addSp .r12 0, .load .d .r11 .r12 112] ++ entry.drop 2 := rfl
  rw [e]
  refine RelCT.block_append (rel_seqR (rel_taint [] hsp (by simp) (by taint_decide))
    (Runs.of_wp (entryLd_wp A₁)) (Runs.of_wp (entryLd_wp A₂)) fun τ₁ τ₂ ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ => ?_)
  refine rel_taint [.r11, .r12] (by rw [c₁, c₂, hsp]) (fun r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂, hsp]

/-- The tag's address, from its slot. -/
theorem ld18_wp {c : Cx} {s : State} (E : Env c s) (S : Slots c s.mem) :
    WP isa (.block [.load .d .r18 .r14 tagO]) s fun s' => s'.gpr .r18 = c.T ∧ Env c s' ∧ s'.sp = s.sp :=
  wp_ld (a := c.W + BitVec.ofNat 64 240) (by decide) (by decide) (by rw [E.r14]; rfl) (E.perm.wR (by decide))
    fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr, S.tag], E.of_pk (PK.ofUpd u₁), u₁.sp⟩

/-- `tagOut`'s arguments. -/
theorem tagOutBlk_wp {c : Cx} {s : State} (E : Env c s) (S : Slots c s.mem) :
    WP isa (.block [.load .d .r9 .r14 tagO, Impl.AesCbc.PPC64LE.mov .r3 .r14, Impl.AesCbc.PPC64LE.mov .r4 .r15]) s
      fun s' => s'.gpr .r9 = c.T ∧ s'.gpr .r3 = c.W ∧ s'.gpr .r4 = BitVec.ofNat 64 c.tl ∧ Env c s' ∧
        s'.sp = s.sp := by
  refine wp_ld (a := c.W + BitVec.ofNat 64 240) (by decide) (by decide) (by rw [E.r14]; rfl)
    (E.perm.wR (by decide)) fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
  obtain pk₃ : PK s s₃ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofUpd u₃))
  exact ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, S.tag],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.r14],
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.r15], E.of_pk pk₃, pk₃.sp⟩

/-- `vg_aes_ccm_seal` in two runs. -/
theorem seal_rel {c : Cx} {N : Addr} {σ₁ σ₂ : State} (A₁ : Args c N σ₁) (A₂ : Args c N σ₂) (hsp : σ₁.sp = σ₂.sp)
    (hT₁ : Covers [⟨c.T, c.tl⟩] σ₁.wr) (hT₂ : Covers [⟨c.T, c.tl⟩] σ₂.wr) :
    RelCT isa (Eq2 σ₁ σ₂) «seal» TT := by
  have L := A₁.lay
  unfold «seal»
  refine rel_seqR (entry_rel A₁ A₂ hsp) (Runs.of_wp (entry_wp A₁)) (Runs.of_wp (entry_wp A₂))
    fun s₁ t₁ En En' => ?_
  obtain h₁ : s₁.sp = t₁.sp := by rw [En.sp, En'.sp, hsp]
  refine rel_seqR (rel_env [.r5, .r6] En.env En'.env h₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [En.r5, En'.r5]
      · rw [En.r6, En'.r6]) ⟨_, by taint_decide⟩)
    (Runs.of_wp (ctrs_wp L En.env (A₁.nonce.of_eq En.rd En.wr) En.r5 En.r6))
    (Runs.of_wp (ctrs_wp L En'.env (A₂.nonce.of_eq En'.rd En'.wr) En'.r5 En'.r6))
    fun s₂ t₂ ⟨pk₂, f₂, c₂⟩ ⟨pk₂', f₂', c₂'⟩ => ?_
  obtain E₂ := En.env.of_pk pk₂
  obtain E₂' := En'.env.of_pk pk₂'
  obtain h₂ : s₂.sp = t₂.sp := by rw [pk₂.sp, pk₂'.sp, h₁]
  obtain hnl : ∀ m, (bytesAt m N c.nl).length = c.nl := fun m => length_bytesAt _ _ _
  refine rel_seqR (mac_rel L E₂ E₂' h₂ (.inl rfl) (En.slots.mut L (f₂.sub (c0_mut c)))
      (En'.slots.mut L (f₂'.sub (c0_mut c))))
    (Runs.of_wp (mac_wp L E₂ (En.slots.mut L (f₂.sub (c0_mut c))) (hnl _) c₂ (.inl rfl)))
    (Runs.of_wp (mac_wp L E₂' (En'.slots.mut L (f₂'.sub (c0_mut c))) (hnl _) c₂' (.inl rfl)))
    fun s₃ t₃ M M' => ?_
  obtain E₃ := E₂.of_pk M.pk
  obtain E₃' := E₂'.of_pk M'.pk
  obtain h₃ : s₃.sp = t₃.sp := by rw [M.pk.sp, M'.pk.sp, h₂]
  have fM := M.frame
  have fM' := M'.frame
  rw [macR_list] at fM fM'
  obtain c₃ := (Proof.Cmac.bytesAt_frame fM (w_keep L (by decide) (by decide)) (by decide)).trans c₂
  obtain c₃' := (Proof.Cmac.bytesAt_frame fM' (w_keep L (by decide) (by decide)) (by decide)).trans c₂'
  refine rel_seqR (tag_rel L E₃ E₃' h₃ (.inl rfl)) (Runs.of_wp (tag_wp L E₃ (hnl _) c₃ (.inl rfl)))
    (Runs.of_wp (tag_wp L E₃' (hnl _) c₃' (.inl rfl))) fun s₄ t₄ ⟨pk₄, _, f₄, _⟩ ⟨pk₄', _, f₄', _⟩ => ?_
  obtain E₄ := E₃.of_pk pk₄
  obtain E₄' := E₃'.of_pk pk₄'
  obtain h₄ : s₄.sp = t₄.sp := by rw [pk₄.sp, pk₄'.sp, h₃]
  have f₄l := f₄
  have f₄l' := f₄'
  rw [ctrR_list] at f₄l f₄l'
  obtain c₄ := (Proof.Cmac.bytesAt_frame f₄l (w_keep L (by decide) (by decide)) (by decide)).trans c₃
  obtain c₄' := (Proof.Cmac.bytesAt_frame f₄l' (w_keep L (by decide) (by decide)) (by decide)).trans c₃'
  refine rel_seqR (ctr_rel L E₄ E₄' h₄ (hnl _) (hnl _) c₄ c₄') (Runs.of_wp (ctr_wp L E₄ (hnl _) c₄))
    (Runs.of_wp (ctr_wp L E₄' (hnl _) c₄')) fun s₅ t₅ ⟨pk₅, f₅, _⟩ ⟨pk₅', f₅', _⟩ => ?_
  obtain E₅ := E₄.of_pk pk₅
  obtain E₅' := E₄'.of_pk pk₅'
  obtain h₅ : s₅.sp = t₅.sp := by rw [pk₅.sp, pk₅'.sp, h₄]
  obtain S₅ := En.slots.mut L ((((f₂.sub (c0_mut c)).trans (M.frame.sub (macR_mut (.inl rfl)))).trans
    (f₄.sub (ctrR_mut c (.inl rfl)))).trans (f₅.sub (crR_mut c)))
  obtain S₅' := En'.slots.mut L ((((f₂'.sub (c0_mut c)).trans (M'.frame.sub (macR_mut (.inl rfl)))).trans
    (f₄'.sub (ctrR_mut c (.inl rfl)))).trans (f₅'.sub (crR_mut c)))
  obtain wr₅ : s₅.wr = σ₁.wr := by rw [pk₅.wr, pk₄.wr, M.pk.wr, pk₂.wr, En.wr]
  obtain wr₅' : t₅.wr = σ₂.wr := by rw [pk₅'.wr, pk₄'.wr, M'.pk.wr, pk₂'.wr, En'.wr]
  refine rel_seqR ?_ (Runs.of_wp (tagOut_wp L E₅ S₅ (by rw [wr₅]; exact hT₁)))
    (Runs.of_wp (tagOut_wp L E₅' S₅' (by rw [wr₅']; exact hT₂))) fun s₆ t₆ ⟨pk₆, _⟩ ⟨pk₆', _⟩ => ?_
  · unfold tagOut
    refine rel_seqR (rel_env [] E₅ E₅' h₅ (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (tagOutBlk_wp E₅ S₅))
      (Runs.of_wp (tagOutBlk_wp E₅' S₅')) fun τ₁ τ₂ ⟨a₁, b₁, c₁', F₁, sp₁⟩ ⟨a₂, b₂, c₂', F₂, sp₂⟩ => ?_
    refine rel_env [.r3, .r4, .r9] F₁ F₂ (by rw [sp₁, sp₂, h₅]) (fun r hr => ?_) ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [b₁, b₂]
    · rw [c₁', c₂']
    · rw [a₁, a₂]
  · exact rel_env [] (E₅.of_pk pk₆) (E₅'.of_pk pk₆') (by rw [pk₆.sp, pk₆'.sp, h₅]) (by simp) ⟨_, by taint_decide⟩

/-- `vg_aes_ccm_open` in two runs. -/
theorem open_rel {c : Cx} {N : Addr} {σ₁ σ₂ : State} (A₁ : Args c N σ₁) (A₂ : Args c N σ₂) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) «open» TT := by
  have L := A₁.lay
  unfold «open»
  refine rel_seqR (entry_rel A₁ A₂ hsp) (Runs.of_wp (entry_wp A₁)) (Runs.of_wp (entry_wp A₂))
    fun s₁ t₁ En En' => ?_
  obtain h₁ : s₁.sp = t₁.sp := by rw [En.sp, En'.sp, hsp]
  refine rel_seqR (rel_env [.r5, .r6] En.env En'.env h₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [En.r5, En'.r5]
      · rw [En.r6, En'.r6]) ⟨_, by taint_decide⟩)
    (Runs.of_wp (ctrs_wp L En.env (A₁.nonce.of_eq En.rd En.wr) En.r5 En.r6))
    (Runs.of_wp (ctrs_wp L En'.env (A₂.nonce.of_eq En'.rd En'.wr) En'.r5 En'.r6))
    fun s₂ t₂ ⟨pk₂, f₂, c₂⟩ ⟨pk₂', f₂', c₂'⟩ => ?_
  obtain E₂ := En.env.of_pk pk₂
  obtain E₂' := En'.env.of_pk pk₂'
  obtain h₂ : s₂.sp = t₂.sp := by rw [pk₂.sp, pk₂'.sp, h₁]
  obtain hnl : ∀ m, (bytesAt m N c.nl).length = c.nl := fun m => length_bytesAt _ _ _
  refine rel_seqR (ctr_rel L E₂ E₂' h₂ (hnl _) (hnl _) c₂ c₂') (Runs.of_wp (ctr_wp L E₂ (hnl _) c₂))
    (Runs.of_wp (ctr_wp L E₂' (hnl _) c₂')) fun s₃ t₃ ⟨pk₃, f₃, _⟩ ⟨pk₃', f₃', _⟩ => ?_
  obtain E₃ := E₂.of_pk pk₃
  obtain E₃' := E₂'.of_pk pk₃'
  obtain h₃ : s₃.sp = t₃.sp := by rw [pk₃.sp, pk₃'.sp, h₂]
  obtain g₁₃ := (f₂.sub (c0_mut c)).trans (f₃.sub (crR_mut c))
  obtain g₁₃' := (f₂'.sub (c0_mut c)).trans (f₃'.sub (crR_mut c))
  obtain c₃ := (Proof.Cmac.bytesAt_frame f₃ (crR_disj L (.inl (by decide))) (by decide)).trans c₂
  obtain c₃' := (Proof.Cmac.bytesAt_frame f₃' (crR_disj L (.inl (by decide))) (by decide)).trans c₂'
  refine rel_seqR (mac_rel L E₃ E₃' h₃ (.inr rfl) (En.slots.mut L g₁₃) (En'.slots.mut L g₁₃'))
    (Runs.of_wp (mac_wp L E₃ (En.slots.mut L g₁₃) (hnl _) c₃ (.inr rfl)))
    (Runs.of_wp (mac_wp L E₃' (En'.slots.mut L g₁₃') (hnl _) c₃' (.inr rfl))) fun s₄ t₄ M M' => ?_
  obtain E₄ := E₃.of_pk M.pk
  obtain E₄' := E₃'.of_pk M'.pk
  obtain h₄ : s₄.sp = t₄.sp := by rw [M.pk.sp, M'.pk.sp, h₃]
  have fM := M.frame
  have fM' := M'.frame
  rw [macR_list] at fM fM'
  obtain c₄ := (Proof.Cmac.bytesAt_frame fM (w_keep L (by decide) (by decide)) (by decide)).trans c₃
  obtain c₄' := (Proof.Cmac.bytesAt_frame fM' (w_keep L (by decide) (by decide)) (by decide)).trans c₃'
  refine rel_seqR (tag_rel L E₄ E₄' h₄ (.inr rfl)) (Runs.of_wp (tag_wp L E₄ (hnl _) c₄ (.inr rfl)))
    (Runs.of_wp (tag_wp L E₄' (hnl _) c₄' (.inr rfl))) fun s₅ t₅ ⟨pk₅, _, f₅, _⟩ ⟨pk₅', _, f₅', _⟩ => ?_
  obtain E₅ := E₄.of_pk pk₅
  obtain E₅' := E₄'.of_pk pk₅'
  obtain h₅ : s₅.sp = t₅.sp := by rw [pk₅.sp, pk₅'.sp, h₄]
  obtain S₅ := En.slots.mut L ((g₁₃.trans (M.frame.sub (macR_mut (.inr rfl)))).trans (f₅.sub (ctrR_mut c (.inr rfl))))
  obtain S₅' := En'.slots.mut L ((g₁₃'.trans (M'.frame.sub (macR_mut (.inr rfl)))).trans
    (f₅'.sub (ctrR_mut c (.inr rfl))))
  refine rel_seqR (rel_env [] E₅ E₅' h₅ (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (ld18_wp E₅ S₅))
    (Runs.of_wp (ld18_wp E₅' S₅')) fun s₆ t₆ ⟨a₁, F₁, sp₁⟩ ⟨a₂, F₂, sp₂⟩ => ?_
  exact rel_env [.r18] F₁ F₂ (by rw [sp₁, sp₂, h₅]) (by simp [a₁, a₂]) ⟨_, by taint_decide⟩

theorem seal_ct : ConstantTime isa sealPPC64LE.pre sealPPC64LE.pub «seal» :=
  ct_of fun σ₁ σ₂ h₁ h₂ hq => by
    obtain B₁ := args_of_seal h₁
    obtain B₂ := args_of_seal h₂
    obtain A₂ := args_two B₂.1 hq
    obtain ⟨-, -, -, -, -, -, -, -, qsp, qa⟩ := hq
    exact seal_rel B₁.1 A₂ qsp B₁.2 (by
      simpa only [cxOf, qa 0 (by decide), qa 1 (by decide)] using B₂.2)

theorem open_ct : ConstantTime isa openPPC64LE.pre openPPC64LE.pub «open» :=
  ct_of fun _ _ h₁ h₂ hq => open_rel (args_of_open h₁) (args_two (args_of_open h₂) hq.1)
    hq.1.2.2.2.2.2.2.2.2.1

end VG.Proof.AesCcm.PPC64LE

end

end

/-!
# AES-CCM on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, states satisfying the preconditions, and the shared contracts of
`Spec/Ccm/Contract.lean` with the working space as a last argument
(`Proof/AesCcm/Scratch.lean`), with no stack: a call (`bl`) stores nothing
in memory, and each function saves the return address in the working
space. Then the code in a frame that allocates the working space
(`Verified.stackScratchArgs`): it is the third stack argument, after `tag`
and `tag_len`, so the frame of 2688 bytes holds the frame's own header and
Parameter Save Area, a copy of those two, the address of the working space
and the working space.
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCcm.PPC64LE

/-! ## Correctness and constant time -/

theorem seal_correct (s : State) (hs : sealPPC64LE.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealPPC64LE.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := seal_wp hs
  exact ⟨t, s', he, ha, hp⟩

theorem open_correct (s : State) (hs : openPPC64LE.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openPPC64LE.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := open_wp hs
  exact ⟨t, s', he, ha, hp⟩

/-- A state satisfying the precondition of `vg_aes_ccm_seal`: a 7-byte nonce,
no associated data, no data, a 4-byte tag at `0x5000` and `work` at 0, the
three at `sp + 96`. -/
def sealSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 7 | .r7 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem a := bif Nat.beq a.toNat 0x8061 then 0x50 else bif Nat.beq a.toNat 0x8068 then 4 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x8060, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ccm_open`: as `sealSat`,
with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8060, 24⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0, 2560⟩] }

/-! ## The shared contracts -/

theorem seal_verified :
    Verified PPC64LE.target «seal» (Proof.AesCcm.sealScratchContract PPC64LE.abi) :=
  Verified.of_correct seal_correct seal_ct
      { pre := by
          intro s h
          sig_pre [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
            Proof.AesCcm.sealRoundsPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
            PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop] at h
          sig_split h
          sig_reduce [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
            Proof.AesCcm.sealRoundsPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
            PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
          sig_and_intros
          sig_close
          all_goals first
            | with_reducible assumption
            | sig_disjoint_symm
            | omega
            | bv_omega_arith
        post := by
          sig_implies_post [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
            Proof.AesCcm.sealRoundsPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
            PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
        pub := by
          sig_implies_pub [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
            Proof.AesCcm.sealRoundsPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
            PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
        sat := by
          sig_implies_sat [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
            Proof.AesCcm.sealRoundsPost, sealPPC64LE, sealPre, oneLay, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
            PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
            [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat }

theorem open_verified :
    Verified PPC64LE.target «open» (Proof.AesCcm.openScratchContract PPC64LE.abi) :=
  Verified.of_correct open_correct open_ct
      { pre := by
          intro s h
          sig_pre [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
            Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes, openLeak, args,
            rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop] at h
          sig_split h
          sig_reduce [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
            Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes, openLeak, args,
            rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop]
          sig_and_intros
          sig_close
          all_goals first
            | with_reducible assumption
            | sig_disjoint_symm
            | omega
            | bv_omega_arith
        post := by
          sig_implies_post [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
            Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes, openLeak, args,
            rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop]
        pub := by
          sig_implies_pub [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
            Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes, openLeak, args,
            rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop]
        sat := by
          sig_implies_sat [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
            Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, openPPC64LE, openPre, oneLay, onePub, openRes, openLeak, args,
            rounds, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
            List.range.loop]
            [openSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

/-! ## The working space on the stack -/

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x8060, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesCcm.sealRoundsContract PPC64LE.abi 2688).pre s := by
  implies_sat [Proof.AesCcm.sealRoundsContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Proof.AesCcm.sealRoundsPost,
    PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 «seal»)
      (Proof.AesCcm.sealRoundsContract PPC64LE.abi 2688) :=
  Verified.stackScratchArgs (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.sealPre PPC64LE.abi.ptrBits)
    (post := Proof.AesCcm.sealRoundsPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2688) (m := 2)
    seal_verified (by decide) (by decide) (Proof.AesCcm.sealPre_local _) (Proof.AesCcm.sealPost_local _)
    (Proof.AesCcm.sealPostOut_local _)
    sealFrameSat_pre

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8060, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesCcm.openRoundsContract PPC64LE.abi 2688).pre s := by
  implies_sat [Proof.AesCcm.openRoundsContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Proof.AesCcm.openRoundsPost,
    Spec.Ccm.openLeak, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, openSat, sealSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 «open»)
      (Proof.AesCcm.openRoundsContract PPC64LE.abi 2688) :=
  Verified.stackScratchArgs (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.openPre PPC64LE.abi.ptrBits)
    (post := Proof.AesCcm.openRoundsPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2688) (m := 2)
    (leak := some (Spec.Ccm.openLeak PPC64LE.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.AesCcm.openPre_local _) (Proof.AesCcm.openPost_local _)
    (Proof.AesCcm.openPostOut_local _)
    openFrameSat_pre (hleak := Proof.AesCcm.openLeak_local _)

end VG.Proof.AesCcm.PPC64LE
