import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksEnd

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Sign

structure PositiveXS (p : Params) (D : Nat) (σ : State) (s : State) : Prop where
  k : PositiveIK p D σ s
  r01 : s.gpr .x24 = 0 ∨ s.gpr .x24 = 1
  pass : s.gpr .x24 = 1 → ∃ t < 814, RejT p σ t ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome ∧ PassV p σ (p.ℓ * t) ∧
    bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t) ∧ SignedFam s (yBase p) p.ℓ (Zv p σ (p.ℓ * t)) (-(q:Int)+1) ((q:Int)-1) ∧
    HFam s 5 p.k (Hv p σ (p.ℓ * t))
  fail : s.gpr .x24 = 0 → loopF p σ minBounds minBounds.sign 0 = none

/-- `SampleInBall` did not finish within `minBounds`: `x24 = 0`, `CNT = 1`. -/
structure PositiveEB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : PositiveIK p D σ s
  none : sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none
  x24 : s.gpr .x24 = 0
  cnt : s.mem.readW (pa s (sc oCNT)) 64 = 1
  t_lt : t < 814
  rej : RejT p σ t

def PositiveLP (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop :=
  (s.gpr .x9 ≠ 0 ∧ PositiveIL p D σ (t + 1) s) ∨ (s.gpr .x9 = 0 ∧ PositiveXS p D σ s)

theorem positiveDecEnd {D : Nat} {p : Params} (h3 : Ok3 p) (hp : ParamsOk p) (hc : lChk p = true) {σ : State} {t : Nat} {s : State}
    (h : PositiveEP p D σ t s ∨ PositiveEF p D σ t s ∨ PositiveEB p D σ t s) : WP isa (.block cntDec) s (PositiveLP p D σ t) := by
  simp only [lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, r1⟩, k1⟩, k2⟩, k3⟩, f1⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have hk : PositiveIK p D σ s := by rcases h with h | h | h <;> exact h.k
  have L := hk.d.im.st.lay
  refine WP.mono_syms (cntDec_ok s (L.inW w1) (L.inR r1)) fun s' ⟨⟨hm, hz⟩, k⟩ hy => ?_
  have hf : Frame [⟨pa s (sc oCNT), 8⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hP : PPostB D s s' [(sc oCNT, 8)] := postB_of_keep k (by decide) hf
  have K := hk.step hP hy k1 (by rcases h3 with rfl | rfl | rfl <;> decide)
  have e15 : s'.gpr .x24 = s.gpr .x24 := k.get .x24
  rcases h with h | h | h
  · -- passed
    rw [h.cnt, one_sub_one] at hz
    refine .inr ⟨hz, K, .inr (e15.trans h.x24), fun _ => ⟨t, h.t_lt, h.rej, h.some, h.pass,
      by rw [L.keepBytes hP k3, h.ct], SignedFam.keep L hP f1 h.z, HFam.keep L hP f2 h.h⟩,
      fun h0 => absurd (h0.symm.trans (e15.trans h.x24)) (by decide)⟩
  · -- rejected
    have hr : RejT p σ (t + 1) := Rej.succ _ _ _ _ _ _ _ h.rej (by rw [Nat.zero_add]; exact iter_rej hp h.some h.fail)
    rw [h.cnt, ofNat_sub_one h.t_lt] at hz
    by_cases ht : t = 813
    · subst ht
      refine .inr ⟨hz, K, .inl (e15.trans h.x24),
        fun h1 => absurd (h1.symm.trans (e15.trans h.x24)) (by decide), fun _ => loop_none_exh hr⟩
    · refine .inl ⟨by
        have hne : (BitVec.ofNat 64 (814 - (t + 1))).toNat ≠ 0 := by
          have := h.t_lt; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
        rw [hz]; intro h0; rw [h0] at hne; exact hne rfl, K, by rw [L.keepW hP k2, h.kap], ?_, by have := h.t_lt; omega, hr⟩
      rw [hP.pa (by decide), hm, Mem.readW_writeW_self64, h.cnt, ofNat_sub_one h.t_lt]
  · -- `SampleInBall` failed
    rw [h.cnt, one_sub_one] at hz
    exact .inr ⟨hz, K, .inl (e15.trans h.x24),
      fun h1 => absurd (h1.symm.trans (e15.trans h.x24)) (by decide), fun _ => loop_none_ball h.rej h.none⟩

theorem positiveBallFailure_ok {S : Nat} {p : Params} (hp : Ok3 p) (hc : lChk p=true)
    {σ s : State} {t : Nat} (h : PositiveIB p S σ t s) (h0 : (s.gpr .x0).setWidth 32=0) :
    WP isa (.block (([.movz .x .x24 0 0] : List Instr)++setQ (sc oCNT) 1)) s (PositiveEB p S σ t) := by
  simp only [lChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1,_⟩,k1⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,k0⟩,_⟩,_⟩,_⟩ := hc
  have hz : WP isa (.block [.movz .x .x24 0 0]) s fun u =>
      VG.Proof.MlKem.AArch64.Only [.x24] s u ∧ u.gpr .x24=0 := by
    refine VG.Proof.MlKem.AArch64.wp_movz fun u hu hv => VG.Proof.MlKem.AArch64.wp_nil ⟨hu,hv⟩
  rw [WP.block_append_iff]
  refine WP.mono_syms hz fun u ⟨hu,hflag⟩ hy => ?_
  have hpu : PPostB S s u [] := postB24 hu []
  have ku := h.c.masks.l.k.step hpu hy k0 (by simp)
  refine WP.mono_syms (setQ_ok ku.d.im.st.lay (by decide) (by decide) w1 (by decide))
    fun v ⟨hpv,hv,hm⟩ hyv => ?_
  exact ⟨ku.step hpv hyv k1 (by rcases hp with rfl | rfl | rfl <;> decide),h.bad h0,
    by rw [hv.get .x24,hflag],
    by rw [hpv.pa (by decide),hm,Mem.readW_writeW_self64]; rfl,h.c.masks.l.t_lt,h.c.masks.l.rej⟩

/-- A successful loop exit supplies accepted signed responses for packing. -/
theorem PositiveXS.outputReady {p : Params} {S : Nat} {σ s : State}
    (h : PositiveXS p S σ s) (h1 : s.gpr .x24=1) :
    ∃t,AcceptedConversion p S σ (p.ℓ*t) (-(q:Int)+1) ((q:Int)-1) 0 s ∧ PassV p σ (p.ℓ*t) := by
  obtain ⟨t,_,_,_,hpass,hct,hz,hh⟩ := h.pass h1
  exact ⟨t,⟨⟨⟨h.k.d.im.st,h.k.d.roots⟩,by intro j hj; omega,
    fun j _ hj => hz j hj,h1⟩,hct,hh⟩,hpass⟩

end VG.Proof.MlDsa.AArch64.Sign
