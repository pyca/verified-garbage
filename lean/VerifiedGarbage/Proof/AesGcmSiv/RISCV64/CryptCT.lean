module

import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Rel
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Crypt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Rel
meta import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Crypt
meta import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
public import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-!
# AES-GCM-SIV on RISC-V: the tag and counter mode in two runs

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcmSiv/PPC64LE/CryptCT.lean`): `tag o` and `crypt`, run from
two states in the same environment, leak the same: the code between calls
by the taint analysis (`rel_env`), from the pointer `s9` and the count
`s10`, which are public in both runs, and each call of `vg_aes_ctr32` by its
proof (`rel_ctr`). The loop of blocks relates two runs after the same number
of blocks, which the correctness proofs describe (`BlocksPost`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.Impl.AesGcmSiv.RISCV64 VG.RISCV64
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_ite)
open VG.Proof.AesCcm.RISCV64 (Runs Runs.of_wp Runs.mono Runs.and rel_seqR rel_of_eq2 rel_post)
open VG.Spec.Aes (bytesAt)

/-- `tag o`. -/
theorem tag_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
    {o : Nat} (ho : o = 0 ∨ o = 240) : RelCT isa (Eq2 σ₁ σ₂) (tag o) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ []))
      (.block (copy16 cbO ccO ++ zero16 o ++ ctrArgs ++ ([.addi .a3 .s0 o, .li .a4 1] : List Instr))) h).isSome
        = true := by
    rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold tag
  exact rel_seqR (rel_env [] E₁ E₂ hsp (by simp) t) (Runs.of_wp (tagArgs_wp L E₁ ho))
    (Runs.of_wp (tagArgs_wp L E₂ ho)) fun τ₁ τ₂ ⟨pk₁, _, C₁, _⟩ ⟨pk₂, _, C₂, _⟩ =>
      rel_ctr C₁ C₂ (by rw [pk₁.sp, pk₂.sp, hsp])

/-- One block, from two runs after the same number `j` of blocks. -/
theorem cryptBlock_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂)
    (hsp : σ₁.sp = σ₂.sp) {j : Nat} (hj : 16 * (j + 1) ≤ c.n)
    (h9₁ : σ₁.gpr .s9 = c.D + BitVec.ofNat 64 (16 * j)) (h9₂ : σ₂.gpr .s9 = c.D + BitVec.ofNat 64 (16 * j))
    (h10₁ : σ₁.gpr .s10 = BitVec.ofNat 64 (c.n - 16 * j)) (h10₂ : σ₂.gpr .s10 = BitVec.ofNat 64 (c.n - 16 * j)) :
    RelCT isa (Eq2 σ₁ σ₂) cryptBlock TT := by
  unfold cryptBlock
  refine rel_seqR (rel_env [.s9] E₁ E₂ hsp (by simp [h9₁, h9₂]) ⟨_, by taint_decide⟩)
    (Runs.of_wp (blkArgs_wp L E₁ hj h9₁)) (Runs.of_wp (blkArgs_wp L E₂ hj h9₂))
    fun τ₁ τ₂ ⟨pk₁, _, C₁, s9₁, s10₁⟩ ⟨pk₂, _, C₂, s9₂, s10₂⟩ => ?_
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp]
  refine rel_seqR (rel_ctr C₁ C₂ hsp₁) (ctr_runs (E₁.of_pk pk₁) C₁) (ctr_runs (E₂.of_pk pk₂) C₂)
    fun ω₁ ω₂ G₁ G₂ => ?_
  refine rel_env [.s9, .s10] G₁.1 G₂.1 (by rw [G₁.2.1, G₂.2.1, hsp₁]) (fun r hr => ?_) ⟨_, by taint_decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [G₁.2.2 .s9 (by simp), G₂.2.2 .s9 (by simp), s9₁, s9₂, h9₁, h9₂]
  · rw [G₁.2.2 .s10 (by simp), G₂.2.2 .s10 (by simp), s10₁, s10₂, h10₁, h10₂]

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
  have mid : ∀ {σ τ : State}, Env c σ → HeadPost c σ τ → Runs (.ite (.zero .a7) (.block [])
      (.loop cryptBlock (.nonzero .a7))) τ fun ρ => PK τ ρ ∧ ρ.gpr .s9 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)) ∧
        ρ.gpr .s10 = BitVec.ofNat 64 (c.n - 16 * (c.n / 16)) := fun {σ τ} E H => by
    refine Runs.of_wp (WP.ite (decide (c.n / 16 = 0)) (Steps.eval_zero_ofNat _ _ (by omega) H.a7) (fun ht => ?_) (fun hf => ?_))
    · have h0 : c.n / 16 = 0 := by simpa using ht
      exact WP.block_nil ⟨PK.refl _, by rw [H.s9, h0, Nat.mul_zero, BitVec.add_zero],
        by rw [H.s10, h0, Nat.mul_zero, Nat.sub_zero]⟩
    · have h0 : c.n / 16 ≠ 0 := by simpa using hf
      exact WP.mono (blocks_wp L (E.of_pk H.pk) (Proof.Cmac.bytesAt_length σ.mem c.D c.n) (by omega) H.s9 H.s10
        H.ctr H.data H.ciph) fun ρ B => ⟨B.pk, B.s9, B.s10⟩
  refine rel_seqR ?_ (mid E₁ H₁) (mid E₂ H₂) fun ρ₁ ρ₂ ⟨pk₁, s9₁, s10₁⟩ ⟨pk₂, s9₂, s10₂⟩ => ?_
  · refine rel_ite (Steps.eval_zero_ofNat _ _ (by omega) H₁.a7) (Steps.eval_zero_ofNat _ _ (by omega) H₂.a7) (fun _ => ?_) (fun hf => ?_)
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
          ⟨PK.refl _, by rw [H₁.s9, Nat.mul_zero, BitVec.add_zero], by rw [H₁.s10, Nat.mul_zero, Nat.sub_zero],
            H₁.ctr, by rw [H₁.data, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩,
          ⟨PK.refl _, by rw [H₂.s9, Nat.mul_zero, BitVec.add_zero], by rw [H₂.s10, Nat.mul_zero, Nat.sub_zero],
            H₂.ctr, by rw [H₂.data, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩) fun _ _ h => h
    refine rel_of_eq2 fun a b ⟨j, hk, hj, P₁, P₂⟩ => ?_
    have hc₁ : Spec.GcmSiv.ctxCiph a.mem (c.W + BitVec.ofNat 64 256) c.R =
        Spec.GcmSiv.ctxCiph σ₁.mem (c.W + BitVec.ofNat 64 256) c.R := by rw [ciph_cryR L P₁.frame, H₁.ciph]
    have hc₂ : Spec.GcmSiv.ctxCiph b.mem (c.W + BitVec.ofNat 64 256) c.R =
        Spec.GcmSiv.ctxCiph σ₂.mem (c.W + BitVec.ofNat 64 256) c.R := by rw [ciph_cryR L P₂.frame, H₂.ciph]
    have G₁ := F₁.of_pk P₁.pk
    have G₂ := F₂.of_pk P₂.pk
    refine (rel_post (cryptBlock_rel L G₁ G₂ (by rw [P₁.pk.sp, P₂.pk.sp, hsp₁]) (j := j) (by omega)
        P₁.s9 P₂.s9 P₁.s10 P₂.s10)
      (Runs.of_wp (cryptBlock_wp L G₁ hxl₁ (j := j) (by omega) P₁.s9 P₁.s10 P₁.ctr P₁.data hc₁))
      (Runs.of_wp (cryptBlock_wp L G₂ hxl₂ (j := j) (by omega) P₂.s9 P₂.s10 P₂.ctr P₂.data hc₂))).mono
      (fun _ _ h => h) fun a' b' ⟨Q₁, Q₂⟩ => ?_
    have ev₁ := Steps.eval_nonzero_ofNat _ _ (by omega) Q₁.a7
    have ev₂ := Steps.eval_nonzero_ofNat _ _ (by omega) Q₂.a7
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ⟨c.n / 16 - (j + 1), ?_, j + 1, rfl, ?_,
      ⟨P₁.pk.trans Q₁.pk, Q₁.s9, Q₁.s10, Q₁.ctr, Q₁.data, P₁.frame.trans Q₁.frame⟩,
      ⟨P₂.pk.trans Q₂.pk, Q₂.s9, Q₂.s10, Q₂.ctr, Q₂.data, P₂.frame.trans Q₂.frame⟩⟩⟩
    · rw [ev₁] at ht; simp at ht; omega
    · rw [ev₁] at ht; simp at ht; omega
  · have G₁ := F₁.of_pk pk₁
    have G₂ := F₂.of_pk pk₂
    have hsp₂ : ρ₁.sp = ρ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp₁]
    have q24₁ : ρ₁.gpr .s10 = BitVec.ofNat 64 (c.n % 16) := by rw [s10₁]; congr 1; omega
    have q24₂ : ρ₂.gpr .s10 = BitVec.ofNat 64 (c.n % 16) := by rw [s10₂]; congr 1; omega
    refine rel_ite (Steps.eval_zero_ofNat _ _ (by omega) q24₁) (Steps.eval_zero_ofNat _ _ (by omega) q24₂) (fun _ => ?_) (fun _ => ?_)
    · exact rel_env [] G₁ G₂ hsp₂ (by simp) ⟨_, by taint_decide⟩
    unfold cryptTail
    refine rel_seqR (tag_rel L G₁ G₂ hsp₂ (o := 240) (by decide)) (Runs.of_wp (tag_wp L G₁ (o := 240) (by decide)))
      (Runs.of_wp (tag_wp L G₂ (o := 240) (by decide))) fun ω₁ ω₂ T₁ T₂ => ?_
    refine rel_env [.s9, .s10] (G₁.of_pk T₁.pk) (G₂.of_pk T₂.pk) (by rw [T₁.pk.sp, T₂.pk.sp, hsp₂])
      (fun r hr => ?_) ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [T₁.s9, T₂.s9, s9₁, s9₂]
    · rw [T₁.s10, T₂.s10, q24₁, q24₂]

end VG.Proof.AesGcmSiv.RISCV64
