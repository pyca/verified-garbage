import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)
open Message.Optimized (rootRegions rootPairRegions rootsAt rootsAt_syms)
variable {p : Params}

theorem hash_depth (v : Proof.Sha3.AArch64.Permutation) (p : Params) :
    16*(trHash v.callee p).aarch64Depth≤16 ∧
    16*(muHash v.callee (.off oMU)).aarch64Depth≤16 := by
  obtain ⟨ha,hp,hs⟩ := keccak_dle v
  have hd : DLe 1 (trHash v.callee p) := by
    unfold trHash kabs kpad ksqz callA
    dle_tac
  have hm : DLe 1 (muHash v.callee (.off oMU)) := by
    unfold muHash kabs kpad ksqz callA
    dle_tac
  have := hd.le; have := hm.le; omega
/-- The body, between the entry and the exit: its runs end with the same
`x28` and stack pointer. -/
theorem verifyBody_tr (tab : Addr × Addr) (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hV : VerifyFn p c)
    (hp : p ∈ params) :
    RelCT isa (Two (verifyI p) fun L m t => VOk p L m ∧ StaticRoots 16 t ∧ rootsAt t=tab)
      (.seq (trHash v.callee p) (.seq (muHash v.callee (.off oMU)) (callA n c verifyArgs)))
      fun a b => a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp := by
  have th := trHash_tr v (I := verifyI p) (Φ := fun L m t => VOk p L m ∧ StaticRoots 16 t ∧ rootsAt t=tab) (pkLen_ge hp).2
    (fun _ _ _ h => h.1.facts.key)
  have th' := two_wp (I := verifyI p) (Φ := fun L m t => VOk p L m ∧ StaticRoots 16 t ∧ rootsAt t=tab) (Ψ := fun L m t => VOk p L m ∧ TrOk p L m t ∧ StaticRoots 16 t ∧ rootsAt t=tab) th
    fun L g vv m₀ t hL hc ⟨hφ,hr,htab⟩ =>
      WP.mono_syms (hr.phase (hash_depth v p).1 (by decide) (trHash_ok v hL hφ.facts.key hc))
        fun t' ⟨⟨hc',htr⟩,hr'⟩ hsy=>
          ⟨hc',hφ,by unfold TrOk; rw [htr,hφ.facts.key],hr',by rw [rootsAt_syms hsy,htab]⟩
  have side : ∀ L : Lay, L.Ok → (∃ R ∈ L.rd ++ L.wr, Within ⟨L.MU, 64⟩ R) ∧
      Region.Disjoint ⟨L.MU, 64⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.MU, 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.MU, 64⟩ := fun L hL => by
    obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
    exact ⟨⟨R, by simp [hR], hw⟩, st_mu.symm, mu_ks, k_mu hL⟩
  have mh := muHash_tr v (I := verifyI p) (Φ := fun L m t => VOk p L m ∧ TrOk p L m t ∧ StaticRoots 16 t ∧ rootsAt t=tab) (tr := .off oMU)
    (by decide) rfl (fun L => L.MU) (fun L g vv m t hc => hc.off oMU) side
  have mh' := two_wp (I := verifyI p) (Φ := fun L m t => VOk p L m ∧ TrOk p L m t ∧ StaticRoots 16 t ∧ rootsAt t=tab)
    (Ψ := fun L m t => VOk p L m ∧ VMuOk p L m t ∧ StaticRoots 16 t ∧ rootsAt t=tab) mh fun L g vv m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d⟩ := side L hL
      refine WP.mono_syms (hφ.2.2.1.phase (hash_depth v p).2 (by decide)
        (muHash_ok v hL hc (tr := .off oMU) (by decide) rfl (fun t' hc' => hc'.off oMU) a b c d))
        fun t' ⟨⟨hc',hμ⟩,hr'⟩ hsy => ⟨hc',hφ.1,?_,hr',by rw [rootsAt_syms hsy,hφ.2.2.2]⟩
      unfold VMuOk
      rw [hμ]
      have h2 := hφ.2.1
      unfold TrOk at h2
      rw [show L.X + BitVec.ofNat 64 oMU = L.MU from rfl, h2]
  refine RelCT.postDep (F := fun x x' => x'.gpr .x28 = x.gpr .x28 ∧ x'.sp = x.sp)
    (th'.seq (mh'.seq (verifyCall_tr tab hV hp))) (fun x y hxy => ?_) fun x y x' y' hxy f₁ f₂ => ?_
  · have run : ∀ {L : Lay} {g vv m₀} {t : State}, L.Ok → Ctx L g vv m₀ t → (VOk p L m₀ ∧ StaticRoots 16 t ∧ rootsAt t=tab) →
        WP isa (.seq (trHash v.callee p) (.seq (muHash v.callee (.off oMU)) (callA n c verifyArgs))) t
          fun t' => t'.gpr .x28 = t.gpr .x28 ∧ t'.sp = t.sp := fun hL hc ⟨hφ,hr,_⟩ => by
      obtain ⟨σ, hσ, h8, rfl, -⟩ := hφ
      obtain ⟨a, b, c, d⟩ := side _ hL
      refine WP.seq (WP.mono (hr.phase (hash_depth v p).1 (by decide) (trHash_ok v hL rfl hc)) fun t₁ ⟨⟨hc₁,_⟩,hr₁⟩ => ?_)
      refine WP.seq (WP.mono (hr₁.phase (hash_depth v p).2 (by decide) (muHash_ok v hL hc₁ (tr := .off oMU) (by decide) rfl
        (fun t' hc' => hc'.off oMU) a b c d)) fun t₂ ⟨⟨hc₂,_⟩,hr₂⟩ => ?_)
      exact WP.mono (verifyCall_ok hV hp hσ h8 hc₂ hr₂) fun s' ⟨hf, _⟩ =>
        ⟨hf.x28.trans hc.x28.symm, hf.sp.trans hc.sp.symm⟩
    obtain ⟨L, _, _, _, _, _, _, hL, _, c₁, c₂, φ₁, φ₂⟩ := hxy
    exact ⟨run hL c₁ φ₁, run hL c₂ φ₂⟩
  · obtain ⟨L, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := hxy
    exact ⟨by rw [f₁.1, f₂.1, c₁.x28, c₂.x28], by rw [f₁.2, f₂.2, c₁.sp, c₂.sp]⟩


end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
