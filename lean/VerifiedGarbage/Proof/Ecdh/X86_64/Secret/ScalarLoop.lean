import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.ScalarStep

/-! The descending secret-scalar loop terminates with the original scalar multiple. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem scalar_loop_ok {K : WinCfg} {base : Addr} {size k j : Nat}
    (hL : SecretLay K size) (hm : UnitMod Spec.P256.p (2^(64*K.M.n)))
    (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve) (hO : PeerOrder Spec.P256.curve)
    (ht : K.tbl<2^31) (hOne : K.one<Spec.P256.p)
    (hOneVal : toM Spec.P256.p (2^(64*K.M.n)) K.one=1)
    (hj1 : 1≤j) (hj : j<K.J) {P : Point Spec.P256.curve}
    (hP : onCurve Spec.P256.curve P=true) (hne : P≠.infinity)
    {s₀ s : State} (hI : ScalarInv K Spec.P256.curve base size k P s₀ s j) :
    WP isa (.loop (Impl.Ecdh.X86_64.Window5.scalarStep K) .ne) s fun t =>
      ScalarInv K Spec.P256.curve base size k P s₀ t 0 := by
  let I := fun r t => 1≤r ∧ r<K.J ∧ ScalarInv K Spec.P256.curve base size k P s₀ t r
  refine WP.loop (M:=isa) I (fun r u ⟨hr1,hrJ,iu⟩ => ?_) j s ⟨hj1,hj,hI⟩
  refine WP.mono (scalar_step_ok hL hm hC ha hO ht hOne hOneVal hr1 hrJ hP hne iu)
    fun t ⟨it,zt⟩ => ?_
  by_cases he : r=1
  · subst r
    refine Or.inl ⟨?_,it⟩
    change t.zf.map (!·)=some false
    rw [zt]
    rfl
  · refine Or.inr ⟨?_,r-1,by omega,by omega,by omega,it⟩
    change t.zf.map (!·)=some true
    rw [zt]
    simp only [show r-1≠0 by omega,decide_false,Option.map_some,Bool.not_false]

theorem ScalarInv.result {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    {P : Point C} {s₀ s : State} (hI : ScalarInv K C base size k P s₀ s 0) (hk : k<C.n) :
    InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y)
      (tmv C K.M.n base s K.R.z) (mul k P) := by
  simpa only [Window5.winE_zero,recoded,Nat.add_sub_cancel] using hI.acc hk

end VG.Proof.Ecdh.X86_64.Secret
