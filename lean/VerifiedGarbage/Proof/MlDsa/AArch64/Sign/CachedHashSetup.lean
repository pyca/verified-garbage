import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedCommitment
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentPack

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Proof.MlKem.AArch64 (Only wp_ldrx wp_addImm wp_nil)

/-- Exact first block of `Cached.hash`; only x9 changes. -/
theorem hashSetup_run {p : Params} (hp : Ok3 p) (s : State)
    (hr : InRegions (s.rd++s.wr) (pa s (sc oKAP)) 8) :
    WP isa (.block [.ldr .x .x9 .x28 oKAP,.addImm .x .x9 .x9 (2*p.ℓ-1)]) s fun u=>
      Only [.x9] s u ∧ u.gpr .x9=s.mem.readW (pa s (sc oKAP)) 64+BitVec.ofNat 64 (2*p.ℓ-1) := by
  have himm : 2*p.ℓ-1<4096 := by rcases hp with rfl|rfl|rfl <;> decide
  refine wp_ldrx (a:=pa s (sc oKAP)) (by decide) rfl hr fun a ha ea=>
    wp_addImm himm fun b hb eb=>wp_nil ⟨(ha.trans hb).mono (by simp),?_⟩
  rw [eb,ea]

/-- The counter used by the fused commitment/mask helper is the next
iteration's odd-mask index. No truncation or extra loop-range assumption is
needed for this exact 64-bit equality. -/
theorem hashSetup_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (h : PositiveICh p S σ t p.k s) :
    WP isa (.block [.ldr .x .x9 .x28 oKAP,.addImm .x .x9 .x9 (2*p.ℓ-1)]) s fun u=>
      PositiveICh p S σ t p.k u ∧
      u.gpr .x9=BitVec.ofNat 64 (p.ℓ*t+2*p.ℓ-1) ∧ Only [.x9] s u := by
  have hr : inB (sgB p) (sc oKAP) 8=true := by rcases hp with rfl|rfl|rfl <;> decide
  have hk : icwChk p [] p.k=true := by rcases hp with rfl|rfl|rfl <;> decide
  have hw1 : keepB (sgR p) (sgW p) [] (sc oW1) (w1Len p*p.k)=true := by
    rcases hp with rfl|rfl|rfl <;> decide
  have L := h.c.masks.l.st.lay
  refine WP.mono_syms (hashSetup_run hp s (L.inR hr)) fun u ⟨hu,hv⟩ hy=>?_
  have hpu : PPostB S s u [] := postB_of_keep hu.keep (by decide) (by rw [hu.mem]; exact Frame.refl _ _)
  refine ⟨⟨h.c.step hpu hy hk (by simp),?_⟩,?_,hu⟩
  · rw [L.keepBytes hpu hw1,h.w1]
  · rw [hv,h.c.masks.l.kap,ofNat64_add]
    apply congrArg (BitVec.ofNat 64)
    have hl : 1≤2*p.ℓ := by rcases hp with rfl|rfl|rfl <;> decide
    omega

end VG.Proof.MlDsa.AArch64.Sign.Cached
