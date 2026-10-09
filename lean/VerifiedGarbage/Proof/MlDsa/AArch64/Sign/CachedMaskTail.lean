import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMaskCopy
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Proof.MlKem.AArch64 (Only wp_ldrx wp_nil)

theorem tailMask_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) {σ s : State} {t : Nat}
    (h : PositiveICm p S σ t (p.ℓ-1) s) (hm : t=0 ∨ Mask p σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.tailMask P p) s (PositiveICm p S σ t p.ℓ) := by
  have hlen : p.ℓ-1+1=p.ℓ := by rcases hp with rfl|rfl <;> decide
  have hk : inB (sgB p) (sc oKAP) 8=true := by rcases hp with rfl|rfl <;> decide
  have hload : WP isa (.block [.ldr .x .x9 .x28 oKAP]) s fun a=>
      Only [.x9] s a ∧ a.gpr .x9=s.mem.readW (pa s (sc oKAP)) 64 :=
    wp_ldrx (t:=.x9) (n:=.x28) (off:=oKAP) (a:=pa s (sc oKAP)) (by decide) rfl (h.l.st.lay.inR hk) fun a ha va=>wp_nil ⟨ha,va⟩
  unfold Impl.MlDsa.AArch64.Sign.Cached.tailMask
  refine WP.seq (WP.mono_syms hload fun a ⟨ha,va⟩ hya=>?_)
  have hpost : PPostB S s a [] := postB_of_keep ha.keep (by decide) (by rw [ha.mem];exact Frame.refl _ _)
  have hA := h.step hpost hya (by rcases hp with rfl|rfl <;> decide)
  have hmA : t=0 ∨ Mask p σ t a := hm.elim Or.inl fun hh=>Or.inr (by
    unfold Mask at hh ⊢
    rw [ha.mem,hpost.pa (pS_bases _)]
    exact hh)
  refine WP.seq (WP.ite (M:=isa) (a.gpr .x9 != 0) rfl (fun he=>?_) fun _=>?_)
  · have hc : Mask p σ t a := hmA.resolve_left (by
      intro hz
      rw [va,h.l.kap,hz,Nat.mul_zero] at he
      exact absurd he (by decide))
    refine WP.mono (copyMask_phase_ok (copyChk_ok hp) hA hc) fun u ⟨hu,hy⟩=>?_
    have cf : positiveFinishChk p (p.ℓ-1+1) (p.ℓ-1)=true := by rcases hp with rfl|rfl <;> decide
    have hf := WP.mono (positiveFinish_ok (by omega) cf hu hy) fun _ hh=>hh.1
    simpa only [hlen] using hf
  · have cf : positiveMaskChk p (p.ℓ-1)=true := by rcases hp with rfl|rfl <;> decide
    have hf := positiveMaskR_ok hP cf hA
    unfold Impl.MlDsa.AArch64.Sign.Optimized.maskR at hf
    have hh := WP.seq_iff.mp (WP.assoc' hf)
    simpa only [hlen] using hh

end VG.Proof.MlDsa.AArch64.Sign.Cached
