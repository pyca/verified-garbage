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

Untrusted: everything here is checked by Lean. `keys`, run from two states
in the same environment, leaks the same: the code between calls by the
taint analysis (`rel_env`), each call of `vg_aes_encrypt_blocks` and
`vg_aes_expand_key_scratch` by its proof. The
loops of `derive` run for `rounds / 2 - 1` steps, which the environment
fixes, and its call is on that many blocks (`s11`) in both runs.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.Impl.AesGcmSiv.RISCV64 VG.RISCV64
open VG.RISCV64.Steps (wp_li)
open VG.Proof.Gather.RISCV64 (Eq2 TT)
open VG.Proof.AesCcm.RISCV64 (Runs Runs.of_wp Runs.mono Runs.and rel_seqR rel_of_eq2 rel_post)
open VG.Proof.AesGcm.RISCV64 (CtrCall)

/-- `derive`. -/
theorem derive_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) derive TT := by
  unfold derive
  refine rel_seqR (rel_env [] E₁ E₂ hsp (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (build_wp L E₁))
    (Runs.of_wp (build_wp L E₂)) fun τ₁ τ₂ I₁ I₂ => ?_
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [I₁.pk.sp, I₂.pk.sp, hsp]
  refine rel_seqR (rel_env [.s11] I₁.env I₂.env hsp₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [I₁.s11, I₂.s11])
      ⟨_, by taint_decide⟩) (Runs.of_wp (dargs_wp L I₁.env I₁.s11)) (Runs.of_wp (dargs_wp L I₂.env I₂.s11))
    fun ρ₁ ρ₂ ⟨pk₁, _, s11₁, B₁⟩ ⟨pk₂, _, s11₂, B₂⟩ => ?_
  have hsp₂ : ρ₁.sp = ρ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp₁]
  refine rel_seqR (rel_enc B₁ B₂ hsp₂) (enc_runs (I₁.env.of_pk pk₁) B₁) (enc_runs (I₂.env.of_pk pk₂) B₂)
    fun ω₁ ω₂ G₁ G₂ => ?_
  refine rel_env [.s11] G₁.1 G₂.1 (by rw [G₁.2.1, G₂.2.1, hsp₂]) (fun r hr => ?_) ⟨_, by taint_decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [G₁.2.2 .s11 (by simp), G₂.2.2 .s11 (by simp), s11₁, s11₂, I₁.s11, I₂.s11]

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
