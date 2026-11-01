module

public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Rel
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Keys
meta import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Rel
meta import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Keys
public import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
meta import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Derive
meta import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Derive
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Wp
meta import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-!
# AES-GCM-SIV on RISC-V: the keys in two runs

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcmSiv/PPC64LE/KeysCT.lean`): `keys`, run from two states in the
same environment, leaks the same: the code between calls by the taint
analysis (`rel_env`), each call of `vg_aes_ctr32` and
`vg_aes_expand_key_scratch` by its proof. The loop of `derive` relates two
runs after the same number of steps (`DInv`): the counter `s11`, which
addresses the half kept, and the count `a2` it branches on are public.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.Impl.AesGcmSiv.RISCV64 VG.RISCV64
open VG.RISCV64.Steps (wp_li)
open VG.Proof.Gather.RISCV64 (Eq2 TT)
open VG.Proof.AesCcm.RISCV64 (Runs Runs.of_wp Runs.mono Runs.and rel_seqR rel_of_eq2 rel_post)
open VG.Proof.AesGcm.RISCV64 (CtrCall)

/-- The start of `derive`. -/
theorem derive0_wp {c : Cx} {σ : State} (E : Env c σ) : WP isa (.block [.li .s11 0]) σ (DInv c σ 0) :=
  wp_li (by decide) fun t₀ u₀ => WP.block_nil ⟨E.of_pk (PK.ofUpd u₀), PK.ofUpd u₀, u₀.gpr, Nat.zero_le _,
    by rw [u₀.mem]; exact Frame.refl _ _, rfl⟩

/-- A step's block: the call's arguments, and what it keeps. -/
theorem derArgs_runs {c : Cx} (L : Lay c) {σ t : State} {i : Nat} (I : DInv c σ i t) :
    Runs (.block deriveBlock) t fun t' =>
      CtrCall t' c.K (c.W + BitVec.ofNat 64 112) (c.W + BitVec.ofNat 64 240) (c.W + BitVec.ofNat 64 1792) c.R 1 ∧
        Kept c t t' := by
  have hw := L.ww
  refine (Runs.and (Runs.of_wp (derBlock_wp L I.env I.s11))
    (Runs.kept I.env [.t0, .a0, .a1, .a2, .a3, .a4, .a5] (by decide +kernel))).mono
    fun t₁ ⟨⟨_, _, a0, a1, a2, a3, a4, a5, _⟩, K⟩ => ?_
  exact ⟨cargs L K.1 K.1.perm.k (L.k_w' (by decide)) (L.k_w' (by decide)) (L.k_w' (by decide))
    (L.w_w (.inl (by decide)) (by decide) (by decide)) (L.w_w (.inl (by decide)) (by decide) (by decide))
    (K.1.perm.wC (by decide)) (by rw [L.wrapW (by decide)]; omega) (by decide) a0 a1 a2 a3 a4 a5, K⟩

/-- A step of `derive`, from two runs after the same number of steps. -/
theorem derStep_rel {c : Cx} (L : Lay c) {σ₁ σ₂ τ₁ τ₂ : State} {i : Nat} (I₁ : DInv c σ₁ i τ₁)
    (I₂ : DInv c σ₂ i τ₂) (hsp : τ₁.sp = τ₂.sp) :
    RelCT isa (Eq2 τ₁ τ₂) (.seq (.block deriveBlock) (.seq Impl.AesGcm.RISCV64.ctrCall (.block derivePost))) TT := by
  refine rel_seqR (rel_env [.s11] I₁.env I₂.env hsp (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [I₁.s11, I₂.s11])
      ⟨_, by taint_decide⟩) (derArgs_runs L I₁)
    (derArgs_runs L I₂) fun ρ₁ ρ₂ ⟨C₁, K₁⟩ ⟨C₂, K₂⟩ => ?_
  have hsp₁ : ρ₁.sp = ρ₂.sp := by rw [K₁.2.1, K₂.2.1, hsp]
  refine rel_seqR (rel_ctr C₁ C₂ hsp₁) (ctr_runs K₁.1 C₁) (ctr_runs K₂.1 C₂) fun ω₁ ω₂ G₁ G₂ => ?_
  refine rel_env [.s11] G₁.1 G₂.1 (by rw [G₁.2.1, G₂.2.1, hsp₁]) (fun r hr => ?_) ⟨_, by taint_decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [G₁.2.2 .s11 (by simp), G₂.2.2 .s11 (by simp), K₁.2.2 .s11 (by simp), K₂.2.2 .s11 (by simp), I₁.s11, I₂.s11]

/-- `derive`. -/
theorem derive_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) derive TT := by
  have hR := L.rounds
  unfold derive
  refine rel_seqR (rel_env [] E₁ E₂ hsp (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (derive0_wp E₁))
    (Runs.of_wp (derive0_wp E₂)) fun τ₁ τ₂ I₁ I₂ => ?_
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [I₁.pk.sp, I₂.pk.sp, hsp]
  refine (RelCT.loop (Q := TT) (fun m (a b : State) => ∃ i, m = c.R / 2 - 1 - i ∧ i < c.R / 2 - 1 ∧
      DInv c σ₁ i a ∧ DInv c σ₂ i b ∧ a.sp = b.sp) (fun m => ?_) (c.R / 2 - 1 - 0)).mono
    (fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨0, rfl, by rcases hR with h | h <;> rw [h] <;> decide, I₁, I₂, hsp₁⟩) fun _ _ h => h
  refine rel_of_eq2 fun a b ⟨i, hm, hi, J₁, J₂, hab⟩ => ?_
  refine (rel_post (derStep_rel L J₁ J₂ hab) (Runs.of_wp (derStep_wp L hi J₁)) (Runs.of_wp (derStep_wp L hi J₂))).mono
    (fun _ _ h => h) fun a' b' ⟨⟨I₁', r5₁⟩, ⟨I₂', r5₂⟩⟩ => ?_
  have ev₁ := Steps.eval_nonzero_ofNat _ _ (by rcases hR with h | h <;> rw [h] <;> omega) r5₁
  have ev₂ := Steps.eval_nonzero_ofNat _ _ (by rcases hR with h | h <;> rw [h] <;> omega) r5₂
  have hsp' : a'.sp = b'.sp := by rw [I₁'.pk.sp, I₂'.pk.sp, hsp]
  refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ⟨c.R / 2 - 1 - (i + 1), ?_, i + 1, rfl, ?_, I₁', I₂', hsp'⟩⟩
  · rw [ev₁] at ht; simp at ht; omega
  · rw [ev₁] at ht; simp at ht; omega

/-- `expand`'s block: the call's arguments, and what it keeps. -/
theorem expArgs_runs {c : Cx} (L : Lay c) {t : State} (E : Env c t) :
    Runs (.block expandArgs) t fun t' =>
      Proof.AesGcm.RISCV64.KeyCall t' (c.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen c.R) (c.W + BitVec.ofNat 64 256)
        (c.W + BitVec.ofNat 64 1792) ∧ Kept c t t' :=
  (Runs.and (Runs.of_wp (expArgs_wp L E)) (Runs.kept E [.a0, .a1, .a2, .a3] (by decide +kernel))).mono
    fun _ ⟨⟨_, _, kc⟩, K⟩ => ⟨kc, K⟩

/-- `keys`. -/
theorem keys_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) keys TT := by
  unfold keys
  refine rel_seqR (derive_rel L E₁ E₂ hsp) (Runs.of_wp (derive_wp L E₁)) (Runs.of_wp (derive_wp L E₂))
    fun τ₁ τ₂ I₁ I₂ => ?_
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [I₁.pk.sp, I₂.pk.sp, hsp]
  refine rel_seqR ?_ (Runs.of_wp (expand_wp L I₁.env)) (Runs.of_wp (expand_wp L I₂.env)) fun ρ₁ ρ₂ X₁ X₂ => ?_
  · unfold expand
    refine rel_seqR (rel_env [] I₁.env I₂.env hsp₁ (by simp) ⟨_, by taint_decide⟩) (expArgs_runs L I₁.env)
      (expArgs_runs L I₂.env) fun ω₁ ω₂ ⟨k₁, K₁⟩ ⟨k₂, K₂⟩ => ?_
    exact rel_key k₁ k₂ (by rw [K₁.2.1, K₂.2.1, hsp₁])
  · exact rel_env [] (I₁.env.of_pk X₁.pk) (I₂.env.of_pk X₂.pk) (by rw [X₁.pk.sp, X₂.pk.sp, hsp₁]) (by simp)
      ⟨_, by taint_decide⟩

end VG.Proof.AesGcmSiv.RISCV64
