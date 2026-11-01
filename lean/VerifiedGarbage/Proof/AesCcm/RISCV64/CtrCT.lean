module

import VerifiedGarbage.Proof.AesCcm.RISCV64.CallArgs
import VerifiedGarbage.Proof.AesCcm.RISCV64.Crypt
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.CallArgs
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Crypt
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Tag
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.AesCcm.RISCV64
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Chunk
public import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
import VerifiedGarbage.Proof.AesCcm.RISCV64.Rel
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Rel
meta import VerifiedGarbage.Impl.AesCcm.RISCV64
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Chunk
import VerifiedGarbage.Proof.AesCcm.RISCV64.B0
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.B0
import VerifiedGarbage.Proof.AesCcm.RISCV64.Tag
public import VerifiedGarbage.Spec.Ccm
import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp

/-!
# AES-CCM on RISCV64: the tag and counter mode in two runs

Untrusted: everything here is checked by Lean. `tag y`, `ctrChunk`,
`ctrTail` and `ctr`, run from two states in the same environment, leak the
same: the code between calls by the taint analysis (`rel_env`), and each
call of `vg_aes_ctr32` by its proof (`rel_ctr`). The loop over the chunks
relates two runs after the same number of blocks, which the correctness
proofs describe (`CtrInv`): the registers it branches on and the arguments
of the calls are functions of the public values.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.Impl.AesCcm.RISCV64 VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_ite)
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Spec.Aes (bytesAt)

/-- Before the chunks: `s5`, `s6` and `s7` at the start of the data. -/
theorem ctrHeadBlk_wp {c : Cx} (L : Lay c) {nonce : List Byte} {s : State} (E : Env c s) :
    WP isa (.block [mov .s5 .s9, .shift .srl .d .s6 .s10 4, .li .s7 1]) s (CtrInv c nonce s 0) := by
  have hn64 := L.n_lt
  refine wp_mv fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ => wp_li (imm := 1) (by decide) fun s₃ u₃ => WP.block_nil ?_
  exact
    { pk := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofUpd u₃))
      s5 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, E.s9]; exact (BitVec.add_zero _).symm
      s6 := by
        rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s10,
          ofNat_lsr4 hn64, Nat.sub_zero]
      s7 := u₃.gpr
      le := Nat.zero_le _
      frame := by rw [u₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _
      done := rfl
      rest := by rw [u₃.mem, u₂.mem, u₁.mem] }

/-- The length of the data's last bytes. -/
theorem lastLen_wp {c : Cx} {s : State} (E : Env c s) :
    WP isa (.block [.logicImm .and .s8 .s10 15]) s fun s' =>
      s'.gpr .s8 = s.gpr .s10 &&& BitVec.ofInt 64 15 ∧ Env c s' ∧ s'.sp = s.sp ∧
        ∀ r ∈ [Reg.s5, .s7], s'.gpr r = s.gpr r := by
  refine wp_andi (by decide) fun s₂ u₂ => WP.block_nil ?_
  have pk₂ : PK s s₂ := PK.ofUpd u₂
  refine ⟨u₂.gpr, E.of_pk pk₂, pk₂.sp, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> rw [u₂.other _ (by decide)]

section
variable {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
include L E₁ E₂ hsp

/-- `tag y`. -/
theorem tag_rel {y : Nat} (hy : y = 0 ∨ y = 96) : RelCT isa (Eq2 σ₁ σ₂) (tag y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ []))
      (.block ([.li .t3 0] ++ ctrAt ++ ctrArgs ++ [.addi .a3 .s1 (y : Int), .li .a4 1])) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have run : ∀ {σ : State}, Env c σ →
      Runs (.block ([.li .t3 0] ++ ctrAt ++ ctrArgs ++ [.addi .a3 .s1 (y : Int), .li .a4 1])) σ fun s' =>
        Proof.AesCtr.RISCV64.CtrCall s' c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 y)
          (c.W + BitVec.ofNat 64 384) c.R 1 ∧ Kept c σ s' := fun E => by
    rw [List.append_assoc]
    exact Runs.block_append (Runs.kept E [.t1, .t2, .t3] (by decide +kernel)) fun s' K =>
      (Runs.of_wp (ctrArgsW_wp L K.1 (d := y) (by omega) (by omega))).mono fun _ ⟨C, K'⟩ => ⟨C, K.trans K'⟩
  unfold tag
  exact rel_seqR (rel_env [] E₁ E₂ hsp (by simp) t) (run E₁) (run E₂)
    fun τ₁ τ₂ ⟨C₁, K₁⟩ ⟨C₂, K₂⟩ => rel_ctr C₁ C₂ (by rw [K₁.2.1, K₂.2.1, hsp])

/-- `ctrTail`, from two states that agree on where the last bytes are, how
many there are, and the counter. -/
theorem ctrTail_rel (hr : ∀ r ∈ [Reg.s5, .s7, .s8], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) ctrTail TT := by
  have run : ∀ {σ : State}, Env c σ →
      Runs (.block ([mov .t3 .s7] ++ ctrAt ++ zero16 ksO ++ ctrArgs ++ [.addi .a3 .s1 (ksO : Int), .li .a4 1])) σ
        fun s' => Proof.AesCtr.RISCV64.CtrCall s' c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 80)
          (c.W + BitVec.ofNat 64 384) c.R 1 ∧ Kept c σ s' := fun E => by
    rw [List.append_assoc]
    exact Runs.block_append (Runs.kept E [.t0, .t1, .t2, .t3] (by decide +kernel)) fun s' K =>
      (Runs.of_wp (ctrArgsW_wp L K.1 (d := 80) (by decide) (by decide))).mono fun _ ⟨C, K'⟩ => ⟨C, K.trans K'⟩
  unfold ctrTail
  refine rel_seqR (rel_env [.s7] E₁ E₂ hsp (by simpa using hr .s7 (by simp)) ⟨_, by taint_decide⟩)
    (run E₁) (run E₂) fun τ₁ τ₂ ⟨C₁, K₁⟩ ⟨C₂, K₂⟩ => ?_
  refine rel_seqR (rel_ctr C₁ C₂ (by rw [K₁.2.1, K₂.2.1, hsp])) (ctr_runs K₁.1 C₁) (ctr_runs K₂.1 C₂)
    fun ρ₁ ρ₂ G₁ G₂ => ?_
  have a₁ := K₁.trans G₁
  have a₂ := K₂.trans G₂
  refine rel_env [.s5, .s8] G₁.1 G₂.1 (by rw [a₁.2.1, a₂.2.1, hsp]) (fun r hr' => ?_) ⟨_, by taint_decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · rw [a₁.2.2 .s5 (by simp), a₂.2.2 .s5 (by simp), hr .s5 (by simp)]
  · rw [a₁.2.2 .s8 (by simp), a₂.2.2 .s8 (by simp), hr .s8 (by simp)]

/-- One chunk, from two states after the same number `b` of blocks. -/
theorem chunk_rel {b : Nat} (hb : b < c.n / 16)
    (h18₁ : σ₁.gpr .s5 = c.D + BitVec.ofNat 64 (16 * b)) (h18₂ : σ₂.gpr .s5 = c.D + BitVec.ofNat 64 (16 * b))
    (h19₁ : σ₁.gpr .s6 = BitVec.ofNat 64 (c.n / 16 - b)) (h19₂ : σ₂.gpr .s6 = BitVec.ofNat 64 (c.n / 16 - b))
    (h20₁ : σ₁.gpr .s7 = BitVec.ofNat 64 (1 + b)) (h20₂ : σ₂.gpr .s7 = BitVec.ofNat 64 (1 + b)) :
    RelCT isa (Eq2 σ₁ σ₂) ctrChunk TT := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  unfold ctrChunk
  refine RelCT.assoc (rel_seqR (rel_env [.s6, .s7] E₁ E₂ hsp (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h19₁, h19₂]
      · rw [h20₁, h20₂]) ⟨_, by taint_decide⟩)
    (Runs.of_wp (kSel_wp (b := b) h19₁ h20₁ (by omega) (by omega)))
    (Runs.of_wp (kSel_wp (b := b) h19₂ h20₂ (by omega) (by omega)))
    fun τ₁ τ₂ ⟨s8₁, pk₁, _, k₁⟩ ⟨s8₂, pk₂, _, k₂⟩ => ?_)
  obtain ⟨k, hk⟩ : ∃ k, k = min (c.n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) := ⟨_, rfl⟩
  rw [← hk] at s8₁ s8₂
  have hk1 : 1 ≤ k := by rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega
  have hkb : b + k ≤ c.n / 16 := by rw [hk]; omega
  have F₁ := E₁.of_pk pk₁
  have F₂ := E₂.of_pk pk₂
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp]
  have run : ∀ {σ τ : State}, Env c τ → σ.gpr .s5 = c.D + BitVec.ofNat 64 (16 * b) →
      (∀ r ∈ [Reg.s5, .s6, .s7], τ.gpr r = σ.gpr r) → τ.gpr .s8 = BitVec.ofNat 64 k →
      Runs (.block ([mov .t3 .s7] ++ ctrAt ++ ctrArgs ++ [mov .a3 .s5, mov .a4 .s8])) τ fun s' =>
        Proof.AesCtr.RISCV64.CtrCall s' c.K (c.W + BitVec.ofNat 64 64) (c.D + BitVec.ofNat 64 (16 * b))
          (c.W + BitVec.ofNat 64 384) c.R k ∧ Kept c τ s' := fun F hs5 kk hs8 => by
    rw [List.append_assoc]
    exact Runs.block_append (Runs.kept F [.t1, .t2, .t3] (by decide +kernel)) fun s' K =>
      (Runs.of_wp (ctrArgsD_wp L K.1 hk1 hkb (by rw [K.2.2 .s5 (by simp), kk .s5 (by simp), hs5])
        (by rw [K.2.2 .s8 (by simp), hs8]))).mono fun _ ⟨C, K'⟩ => ⟨C, K.trans K'⟩
  refine rel_seqR (rel_env [] F₁ F₂ hsp₁ (by simp) ⟨_, by taint_decide⟩) (run F₁ h18₁ k₁ s8₁)
    (run F₂ h18₂ k₂ s8₂) fun ρ₁ ρ₂ ⟨C₁, K₁⟩ ⟨C₂, K₂⟩ => ?_
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
    have e₁ := eval_z (a := c.n / 16) (by rw [I₁.s6, Nat.sub_zero]) (by omega)
    have e₂ := eval_z (a := c.n / 16) (by rw [I₂.s6, Nat.sub_zero]) (by omega)
    refine rel_ite e₁ e₂ (fun _ => ?_) (fun hf => ?_)
    · exact rel_env [] (E₁.of_pk I₁.pk) (E₂.of_pk I₂.pk) (by rw [I₁.pk.sp, I₂.pk.sp, hsp]) (by simp)
        ⟨_, by taint_decide⟩
    have h0 : c.n / 16 ≠ 0 := by simpa using hf
    refine (RelCT.loop (Q := TT) (fun m a b => ∃ j, m = c.n / 16 - j ∧ j < c.n / 16 ∧
        CtrInv c n₁ σ₁ j a ∧ CtrInv c n₂ σ₂ j b) (fun m => ?_) (c.n / 16 - 0)).mono
      (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨0, rfl, by omega, I₁, I₂⟩) fun _ _ h => h
    refine rel_of_eq2 fun a b ⟨j, hm, hj, J₁, J₂⟩ => ?_
    refine (rel_post (chunk_rel L (E₁.of_pk J₁.pk) (E₂.of_pk J₂.pk) (by rw [J₁.pk.sp, J₂.pk.sp, hsp]) hj
        J₁.s5 J₂.s5 J₁.s6 J₂.s6 J₁.s7 J₂.s7)
      (Runs.of_wp (chunk_wp L hn₁ E₁ hc₁ J₁ hj)) (Runs.of_wp (chunk_wp L hn₂ E₂ hc₂ J₂ hj))).mono
      (fun _ _ h => h) fun a' b' ⟨⟨k, hk, hk1, hkb, K₁⟩, ⟨k', hk', _, _, K₂⟩⟩ => ?_
    have e : k = k' := by rw [hk, hk']
    subst e
    have ev₁ := eval_nz (r := .s6) (a := c.n / 16 - (j + k)) K₁.s6 (by omega)
    have ev₂ := eval_nz (r := .s6) (a := c.n / 16 - (j + k)) K₂.s6 (by omega)
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ⟨c.n / 16 - (j + k), ?_, j + k, rfl, ?_, K₁, K₂⟩⟩
    · rw [ev₁] at ht; simp at ht; omega
    · rw [ev₁] at ht; simp at ht; omega
  · have F₁ := E₁.of_pk I₁.pk
    have F₂ := E₂.of_pk I₂.pk
    have hsp₁ : τ₁.sp = τ₂.sp := by rw [I₁.pk.sp, I₂.pk.sp, hsp]
    refine rel_seqR (rel_env [] F₁ F₂ hsp₁ (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (lastLen_wp F₁))
      (Runs.of_wp (lastLen_wp F₂)) fun ρ₁ ρ₂ ⟨s8₁, G₁, sp₁, k₁⟩ ⟨s8₂, G₂, sp₂, k₂⟩ => ?_
    have hsp₂ : ρ₁.sp = ρ₂.sp := by rw [sp₁, sp₂, hsp₁]
    have q21 : ρ₁.gpr .s8 = ρ₂.gpr .s8 := by rw [s8₁, s8₂, F₁.s10, F₂.s10]
    refine rel_iteZ q21 (rel_env [] G₁ G₂ hsp₂ (by simp) ⟨_, by taint_decide⟩) ?_
    refine ctrTail_rel L G₁ G₂ hsp₂ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [k₁ .s5 (by simp), k₂ .s5 (by simp), I₁.s5, I₂.s5]
    · rw [k₁ .s7 (by simp), k₂ .s7 (by simp), I₁.s7, I₂.s7]
    · exact q21

end VG.Proof.AesCcm.RISCV64
