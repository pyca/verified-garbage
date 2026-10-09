import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedNtt
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRestState
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCalls

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)

theorem nttSecret_ok {S' : Nat} {p : Params} (hF : PFacts p) {σ : State}
    (hp : kgPre p S' σ) {j : Nat} (hj : j < p.ℓ) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : PositiveKR p σ A S R (p.ℓ + p.k) j 0 s) (roots : Sign.StaticRoots S' s) :
    WP isa (nttSecret p j) s fun t => PositiveKR p σ A S R (p.ℓ+p.k) (j+1) 0 t ∧ Sign.StaticRoots S' t := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.kc.lay hF hp
  have hS := h.s1 j hj
  rw [ifn (Nat.lt_irrefl j)] at hS
  have hr : inB (kgR++kgW p) (sP p j) 1024=true := by layd
  have hw : inB (kgW p) (sP p j) 1024=true := by layd
  refine WP.mono_syms (Sign.positiveNttAt_layout L hr hw
    ⟨roots.nttTableAt (L.inW hw),roots.forward.readable⟩ hS.1)
    fun s' ⟨hP',x',hb⟩ hy => ?_
  refine ⟨?_,roots.step_layout L hP' hy (fun w hw' => by
    obtain rfl := List.mem_singleton.mp hw'
    exact hw)⟩
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  exact ⟨h.kc.step hF hp hP' (by unfold kcChk; layd), x'.trans h.x24, h.good,
    h.small, fun e he => L.keepPoly hP' (by layd) (h.aS e he),
    fun i hi => L.keepPoly hP' (by layd) (h.s2 i hi),
    fun j' hj' => if e : j' = j then by
        subst e; rw [ifp (Nat.lt_succ_self j'), hP'.pa (p := sP p j') (show Reg.x28 ∈ keptRegs by decide), ← hS.2]
        exact hb
      else by
        have hv := h.s1 j' hj'
        by_cases hlt : j' < j
        · simp only [ite_eq_left hlt] at hv
          simp only [ite_eq_left (show j' < j+1 by omega)]
          exact Sign.keepPosPoly L hP' (by layd) hv
        · simp only [ite_eq_right hlt] at hv
          simp only [ite_eq_right (show ¬ j' < j+1 by omega)]
          exact L.keepPoly hP' (by layd) hv,
    by rw [L.keepBytes hP' (by layd)]; exact h.pk0,
    by rw [L.keepBytes hP' (by layd)]; exact h.sk0,
    by rw [L.keepBytes hP' (by layd)]; exact h.sk1,
    fun r hr => by
      have : lenS p * r + lenS p ≤ lenS p * (p.ℓ + p.k) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      rw [L.keepBytes hP' (by rcases hlen with hlen | hlen <;> lay [hF.pk, hF.sk, hlen])]; exact h.packs r hr,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩


end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
