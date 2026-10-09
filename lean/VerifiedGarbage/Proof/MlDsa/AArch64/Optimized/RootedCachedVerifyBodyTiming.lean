import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyHash

namespace VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots)
open Message.Optimized (rootsAt)
variable {p : Params}

/-- Hashing the cached digest and verifying preserve the common layout. -/
theorem verifyBody_tr (tab : Addr × Addr) (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hV : Message.OptimizedVerify.VerifyFn p c)
    (hp : p ∈ params) :
    RelCT isa (Two (verifyI p) fun L m t => VOk p L m ∧ StaticRoots 16 t ∧ rootsAt t=tab)
      (.seq (muHash v.callee (.slot fRnd)) (callA n c verifyArgs))
      fun a b => a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp := by
  refine RelCT.postDep (F := fun x x' => x'.gpr .x28 = x.gpr .x28 ∧ x'.sp = x.sp)
    ((cachedMu_tr tab v).seq (verifyCall_tr tab hV hp)) (fun x y hxy => ?_) fun x y x' y' hxy f₁ f₂ => ?_
  · have run : ∀ {L : VG.Proof.MlDsa.AArch64.Message.Lay} {g vv m₀} {t : State},
        L.Ok → Ctx L g vv m₀ t → (VOk p L m₀ ∧ StaticRoots 16 t ∧ rootsAt t=tab) →
        WP isa (.seq (muHash v.callee (.slot fRnd)) (callA n c verifyArgs)) t
          fun t' => t'.gpr .x28 = t.gpr .x28 ∧ t'.sp = t.sp := fun hL hc ⟨hφ,hr,_⟩ => by
      obtain ⟨a, b, c, d⟩ := hφ.trSide.parts
      obtain ⟨σ, hσ, h8, rfl, -⟩ := hφ
      refine WP.seq (WP.mono (hr.phase (hash_depth v) (by decide) (muHash_ok v hL hc (tr := .slot fRnd) (by decide) rfl
        (fun _ hc' => cachedTr_val hc') a b c d)) fun t₂ ⟨⟨hc₂, _⟩,hr₂⟩ => ?_)
      exact WP.mono (verifyCall_ok hV hp hσ h8 hc₂ hr₂) fun s' ⟨hf, _⟩ =>
        ⟨hf.x28.trans hc.x28.symm, hf.sp.trans hc.sp.symm⟩
    obtain ⟨L, _, _, _, _, _, _, hL, _, c₁, c₂, φ₁, φ₂⟩ := hxy
    exact ⟨run hL c₁ φ₁, run hL c₂ φ₂⟩
  · obtain ⟨L, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := hxy
    exact ⟨by rw [f₁.1, f₂.1, c₁.x28, c₂.x28], by rw [f₁.2, f₂.2, c₁.sp, c₂.sp]⟩

end VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
