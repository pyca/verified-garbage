import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedChecksBoundary
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEnd

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
variable {f : Poly}

/-- Sampling writes only the challenge and SHAKE work buffers, retaining the
next iteration's cached odd mask even when sampling exhausts its bound. -/
theorem ball_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hc : bChk p=true) {σ s : State} {t : Nat}
    (roots : Roots p S f s) (h : PositiveIC p S σ t s) :
    WP isa (ballAt P (cLen p) p.τ cP) s fun u=>PositiveIB p S σ t u ∧ Roots p S f u := by
  refine both (positiveBall_ok hP hp hc h) ?_
  simp only [bChk,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1,_⟩,_⟩,hbp⟩ := hc
  refine WP.mono_syms (ballCall_ok hP h.c.masks.l.st.lay hbp c1)
    fun u ⟨hpu,_,_,_,_⟩ hy=>?_
  exact roots.step_layout h.c.masks.l.st.lay hpu hy (challengeWrites_ok hp)
    (by rcases hp with rfl|rfl|rfl <;> decide)

/-- The bounded-sampling failure path changes only the flag and loop counter. -/
theorem ballFailure_ok {S : Nat} {p : Params} (hp : Ok3 p) (hc : lChk p=true)
    {σ s : State} {t : Nat} (roots : Roots p S f s)
    (h : PositiveIB p S σ t s) (h0 : (s.gpr .x0).setWidth 32=0) :
    WP isa (.block (([.movz .x .x24 0 0] : List Instr)++setQ (sc oCNT) 1)) s fun u=>
      PositiveEB p S σ t u ∧ Roots p S f u := by
  refine both (positiveBallFailure_ok hp hc h h0) ?_
  simp only [lChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,k0⟩,_⟩,_⟩,_⟩ := hc
  have hz : WP isa (.block [.movz .x .x24 0 0]) s fun u=>
      VG.Proof.MlKem.AArch64.Only [.x24] s u ∧ u.gpr .x24=0 := by
    refine VG.Proof.MlKem.AArch64.wp_movz fun u hu hv=>VG.Proof.MlKem.AArch64.wp_nil ⟨hu,hv⟩
  rw [WP.block_append_iff]
  refine WP.mono_syms hz fun u ⟨hu,_⟩ hy=>?_
  have hpu : PPostB S s u [] := postB24 hu []
  have ku := h.c.masks.l.k.step hpu hy k0 (by simp)
  have ru := roots.step_layout h.c.masks.l.st.lay hpu hy (by simp) (keep_nil hp)
  refine WP.mono_syms (setQ_ok ku.d.im.st.lay (by decide) (by decide) w1 (by decide))
    fun v ⟨hpv,_,_⟩ hyv=>?_
  exact ru.step_layout ku.d.im.st.lay hpv hyv
    (by rcases hp with rfl|rfl|rfl <;> decide) (by rcases hp with rfl|rfl|rfl <;> decide)

/-- Counter decrement retains the cached polynomial on every loop outcome:
accepted, rejected, or bounded-sampling failure. -/
theorem decEnd_ok {S : Nat} {p : Params} (hp : Ok3 p) (hparam : ParamsOk p)
    (hc : lChk p=true) {σ s : State} {t : Nat} (roots : Roots p S f s)
    (h : PositiveEP p S σ t s ∨ PositiveEF p S σ t s ∨ PositiveEB p S σ t s) :
    WP isa (.block cntDec) s fun u=>PositiveLP p S σ t u ∧ Roots p S f u := by
  refine both (positiveDecEnd hp hparam hc h) ?_
  simp only [lChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1,r1⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩ := hc
  have hk : PositiveIK p S σ s := by rcases h with h|h|h <;> exact h.k
  have L := hk.d.im.st.lay
  refine WP.mono_syms (cntDec_ok s (L.inW w1) (L.inR r1)) fun u ⟨⟨hm,_⟩,k⟩ hy=>?_
  have hf : Frame [⟨pa s (sc oCNT),8⟩] s.mem u.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hpu : PPostB S s u [(sc oCNT,8)] := postB_of_keep k (by decide) hf
  exact roots.step_layout L hpu hy
    (by rcases hp with rfl|rfl|rfl <;> decide) (by rcases hp with rfl|rfl|rfl <;> decide)

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks
