module
public import VerifiedGarbage.Impl.MlDsa.X86_64.Verify.Verify
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTBase
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.PrimsOk

import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTCompute
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTSample
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTStages
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Correct
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA verification on x86-64: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

For primitives `P` that meet their contracts (`PrimsOk`), `verify P p` meets
`verifyContract p` (`verify_verified`): it is correct (`verify_correct`) and
leaks only its inputs, which the contract makes public (`verify_ct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt)

theorem body_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    RelCT isa (RV p fun σ s => T p σ s ∧ s.gpr .r15 = flag True) (body P p) (RV p (T p)) := by
  unfold body
  refine RelCT.seq (hint_tr C hp) (ifOk_rel hp (fun _ _ h => h.1) ?_ ?_ (RelCT.seq (zs_tr C hp)
    (ifOk_rel hp (fun _ _ h => Iz.t h) ?_ ?_ (RelCT.seq (samples_tr C hp)
      (RelCT.mono (compute_tr C hp) ?_ fun _ _ h => h)))))
  · rintro x y ⟨σ₁, σ₂, _, _, pub, i₁, i₂⟩
    rw [S1.r15 i₁, S1.r15 i₂, pub.2.2.2.2.2.2.2.1]
  · intro σ s₀ s hv h₀ hP e hne
    have t₀ := h₀.1
    unfold S1 at h₀
    obtain ⟨_, hm⟩ := h₀
    split at hm
    · rename_i h hh
      obtain ⟨h15, hH⟩ := hm
      obtain ⟨_, _, kh, _⟩ := parChk p hp
      exact ⟨h, hh, t₀.step hp hv hP (tChk_nil p hp), (t₀.lay hp hv).keepHint hP kh hH,
        fun _ h => absurd h (Nat.not_lt_zero _), by rw [e, h15]; exact flag_congr (by simp)⟩
    · exact absurd (by rw [hm]; rfl) hne
  · rintro x y ⟨σ₁, σ₂, _, _, pub, ⟨_, _, hx⟩, ⟨_, _, hy⟩⟩
    rw [hx.r15, hy.r15, pub.2.2.2.2.2.2.2.1]
  · rintro σ s₀ s hv ⟨h, hh, hs⟩ hP e hne
    have hn := flag_ne (by rw [← hs.r15]; exact hne)
    exact ⟨h, ⟨hh, hn⟩, hs.flag hp hv (Nat.le_refl _) hP e, by rw [e, hs.r15]; exact flag_congr (iff_true_intro hn)⟩
  · rintro x y ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, _, hx⟩, ⟨h₂, _, hy⟩⟩
    obtain ⟨q₁, e₁, _, _⟩ := hx.ok
    obtain ⟨q₂, e₂, _, _⟩ := hy.ok
    exact ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, _, q₁, _, hx.toSC e₁⟩, ⟨h₂, _, q₂, _, hy.toSC e₂⟩⟩

theorem verify_ct {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    ConstantTime isa (verifyK p).pre (verifyK p).pub (verify P p) := by
  unfold verify
  exact relStart (RelCT.seq (relInv (I' := fun σ s => T p σ s ∧ s.gpr .r15 = flag True)
    (fun σ s hv hs => by subst hs; exact pro_ok hp hv) pro_tr) (RelCT.seq (body_tr C hp) epi_tr))

end VG.Proof.MlDsa.X86_64.Verify
