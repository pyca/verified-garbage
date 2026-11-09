module

public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Rel
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Keys
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Rel
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Keys
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE
import VerifiedGarbage.Proof.AesCcm.PPC64LE.CallArgs
meta import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.CallArgs
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Derive
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Derive
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Wp
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# AES-GCM-SIV on PPC64LE: the keys in two runs

Untrusted: everything here is checked by Lean. `keys`, run from two states in
the same environment, leaks the same: the code between calls by the taint
analysis (`rel_env`), each call of `vg_aes_ctr32` and
`vg_aes_expand_key_scratch` by its proof. The loop of `derive` relates two
runs after the same number of steps (`DInv`): the counter `r25`, which
addresses the half kept, and the count `r5` it branches on are public.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.Impl.AesGcmSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_li)
open VG.Proof.Gather.PPC64LE (Eq2 TT eval_nonzero)
open VG.Proof.AesCcm.PPC64LE (Runs Runs.of_wp Runs.mono Runs.and Runs.block_append rel_seqR rel_of_eq2 rel_post)
open VG.Proof.AesGcm.PPC64LE (CtrCall)

/-- `derive`. -/
theorem derive_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) derive TT := by
  unfold derive
  refine rel_seqR (rel_env [] E₁ E₂ hsp (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (build_wp L E₁))
    (Runs.of_wp (build_wp L E₂)) fun τ₁ τ₂ I₁ I₂ => ?_
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [I₁.pk.sp, I₂.pk.sp, hsp]
  refine rel_seqR (rel_env [.r25] I₁.env I₂.env hsp₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [I₁.r25, I₂.r25])
      ⟨_, by taint_decide⟩) (Runs.of_wp (dargs_wp L I₁.env I₁.r25)) (Runs.of_wp (dargs_wp L I₂.env I₂.r25))
    fun ρ₁ ρ₂ ⟨pk₁, _, r25₁, B₁⟩ ⟨pk₂, _, r25₂, B₂⟩ => ?_
  have hsp₂ : ρ₁.sp = ρ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp₁]
  refine rel_seqR (rel_enc B₁ B₂ hsp₂) (enc_runs (I₁.env.of_pk pk₁) B₁) (enc_runs (I₂.env.of_pk pk₂) B₂)
    fun ω₁ ω₂ G₁ G₂ => ?_
  refine rel_env [.r25] G₁.1 G₂.1 (by rw [G₁.2.1, G₂.2.1, hsp₂]) (fun r hr => ?_) ⟨_, by taint_decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [G₁.2.2 .r25 (by simp), G₂.2.2 .r25 (by simp), r25₁, r25₂, I₁.r25, I₂.r25]

/-- `expand`'s block: the call's arguments, and what it keeps. -/
theorem expArgs_runs {c : Cx} (L : Lay c) {t : State} (E : Env c t) :
    Runs (.block expandArgs) t fun t' =>
      Proof.AesGcm.PPC64LE.KeyCall t' (c.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen c.R) (c.W + BitVec.ofNat 64 256)
        (c.W + BitVec.ofNat 64 1776) ∧ Kept c t t' :=
  (Runs.and (Runs.of_wp (expArgs_wp L E)) (Runs.kept E [.r3, .r4, .r5, .r6] (by decide +kernel))).mono
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

end VG.Proof.AesGcmSiv.PPC64LE
