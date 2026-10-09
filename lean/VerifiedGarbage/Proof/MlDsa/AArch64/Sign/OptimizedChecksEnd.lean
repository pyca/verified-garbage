import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedResponseState
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputCorrect

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Spec.Sha3 (bytesAt)

structure PositiveEP (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : PositiveIK p D σ s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t)
  z : SignedFam s (yBase p) p.ℓ (Zv p σ (p.ℓ * t)) (-(q:Int)+1) ((q:Int)-1)
  h : HFam s 5 p.k (Hv p σ (p.ℓ * t))
  some : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  pass : PassV p σ (p.ℓ * t)
  x24 : s.gpr .x24 = 1
  cnt : s.mem.readW (pa s (sc oCNT)) 64 = 1
  t_lt : t < 814
  rej : RejT p σ t

/-- Iteration `t` was rejected: `κ = ℓ(t + 1)`, `CNT = 814 - t`. -/
structure PositiveEF (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : PositiveIK p D σ s
  kap : s.mem.readW (pa s (sc oKAP)) 64 = BitVec.ofNat 64 (p.ℓ * (t + 1))
  cnt : s.mem.readW (pa s (sc oCNT)) 64 = BitVec.ofNat 64 (814 - t)
  some : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  fail : ¬ PassV p σ (p.ℓ * t)
  x24 : s.gpr .x24 = 0
  t_lt : t < 814
  rej : RejT p σ t

structure PositiveKO (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  b : PositiveKB p D σ t s
  z : SignedFam s (yBase p) p.ℓ (Zv p σ (p.ℓ * t)) (-(q:Int)+1) ((q:Int)-1)
  h : HFam s 5 p.k (Hv p σ (p.ℓ * t))
  x24 : s.gpr .x24 = bit (PassV p σ (p.ℓ * t))

theorem positiveKBranch_ok {D : Nat} {p : Params} (hp : Ok3 p) (hc : ksChk p = true) {σ : State} {t : Nat} {s : State}
    (h : PositiveKO p D σ t s) :
    WP isa (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p))) s fun s' => PositiveEP p D σ t s' ∨ PositiveEF p D σ t s' := by
  refine ksChk_spec hc fun _ _ _ _ _ _ _ _ _ _ _ c9 c10 _ c14 c15 _ _ c18 c19 c20 c21 _ hl _ _ _ c23 => ?_
  have B7 := h.b
  have L7 := B7.l.st.lay
  refine ifOkElse_ok (fun hne => ?_) fun he => ?_
  · rw [h.x24] at hne
    have hpass := bit_ne.mp hne
    refine WP.mono_syms (setQ_ok L7 (by decide) (by decide) c9 (by decide)) fun s9 ⟨hP9, hcs9, hm9⟩ hy9 => ?_
    exact .inl ⟨B7.l.k.step hP9 hy9 c18 (by rcases hp with rfl | rfl | rfl <;> decide), by rw [L7.keepBytes hP9 c21, B7.ct],
      SignedFam.keep L7 hP9 c14 h.z, HFam.keep L7 hP9 c15 h.h, B7.sampled,
      hpass, by rw [hcs9.get .x24, h.x24]; exact bit_one.mpr hpass,
      by rw [hP9.pa (by decide), hm9, Mem.readW_writeW_self64]; rfl, B7.l.t_lt, B7.l.rej⟩
  · rw [h.x24] at he
    have hfail : ¬ PassV p σ (p.ℓ * t) := fun hp => (bit_ne.mpr hp) he
    refine WP.mono_syms (kapAdd_ok p hl s (L7.inW c10) (L7.inR c23)) fun s9 ⟨hm9, k9⟩ hy9 => ?_
    have hf : Frame [⟨pa s (sc oKAP), 8⟩] s.mem s9.mem := by
      rw [hm9]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hP9' : PPostB D s s9 [(sc oKAP, 8)] := postB_of_keep k9 (by decide) hf
    refine .inr ⟨B7.l.k.step hP9' hy9 c19 (by rcases hp with rfl | rfl | rfl <;> decide), ?_, by rw [L7.keepW hP9' c20, B7.l.cnt], B7.sampled, hfail,
      by rw [k9.get .x24, h.x24]; exact bit_zero.mpr hfail, B7.l.t_lt, B7.l.rej⟩
    rw [hP9'.pa (by decide), hm9, Mem.readW_writeW_self64, B7.l.kap, ofNat64_add, Nat.mul_succ]

/-- A passing checks branch supplies the exact precondition of the
accepted-only conversion and signature-packing phase. -/
theorem PositiveEP.outputReady {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (h : PositiveEP p S σ t s) :
    AcceptedConversion p S σ (p.ℓ*t) (-(q:Int)+1) ((q:Int)-1) 0 s := by
  exact ⟨⟨⟨h.k.d.im.st,h.k.d.roots⟩,by intro j hj; omega,
    fun j _ hj => h.z j hj,h.x24⟩,h.ct,h.h⟩

end VG.Proof.MlDsa.AArch64.Sign
