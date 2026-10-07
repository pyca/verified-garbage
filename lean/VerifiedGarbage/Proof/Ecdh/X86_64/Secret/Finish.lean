import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.ScalarLoop
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Ecdh.XOnly

/-! X-only finalization squares Z, retaining X and the infinity test for the existing inversion. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem square_z_fields_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : SecretLay K size) (hm : UnitMod C.p (2^(64*K.M.n)))
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (·∈slots K) V E s) (hz : K.R.z∈V) :
    WP isa (Impl.Ecdh.X86_64.Window5.fp K.M [.mul K.R.z K.R.z K.R.z]) s fun t =>
      ProgKeep K.M base [K.R.z] s t ∧
      Inv K.M base size C.p (·∈slots K) V (Function.update E K.R.z (E K.R.z*E K.R.z)) t := by
  let ops : List FOp := [.mul K.R.z K.R.z K.R.z]
  have hs : ∀ op∈ops,∀ x∈op.out::op.ins,x∈slots K := by
    intro op hop x hx
    obtain rfl := List.mem_singleton.mp hop
    simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
    subst x
    exact hI.sl _ hz
  have hr : readsOk ops V=true := by simp [ops,readsOk,FOp.ins,hz]
  change WP isa (ForwardField.programB K.M ops) s _
  refine WP.mono (ForwardField.programB_ok hL.n hL.lay hm ops hI hs hr) fun t ⟨kt,it⟩ => ?_
  refine ⟨by simpa only [ops,List.map_cons,List.map_nil,FOp.out] using kt,?_⟩
  have iv := it.sub (V':=V) (fun x hx => (mem_validAfter ops V).mpr (Or.inl hx))
  simpa only [ops,runOps,List.foldl_cons,List.foldl_nil,FOp.run] using iv

structure WindowPost (K : WinCfg) (C : Curve) (base : Addr) (size k : Nat)
    (P : Point C) (s t : State) : Prop where
  field : Inv K.M base size C.p (·∈slots K) (scalarLive K) (tmv C K.M.n base t) t
  keep : CounterKeep K.M base (writes K) s t
  point : k<C.n → XOnly C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.z) (mul k P)

theorem scalar_finish_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : SecretLay K size) (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C)
    {P : Point C} {s₀ s : State} (hI : ScalarInv K C base size k P s₀ s 0) :
    WP isa (Impl.Ecdh.X86_64.Window5.fp K.M [.mul K.R.z K.R.z K.R.z]) s
      (WindowPost K C base size k P s₀) := by
  have vx : K.R.x∈scalarLive K := by simp [scalarLive,jacCoords]
  have vz : K.R.z∈scalarLive K := by simp [scalarLive,jacCoords]
  refine WP.mono (square_z_fields_ok hL hm hI.field vz) fun t ⟨kt,it⟩ => ?_
  have hxz : K.R.x≠K.R.z := by rw [hL.rxz]; omega
  refine ⟨it.to_tmv,hI.keep.trans ((CounterKeep.of_progKeep kt).mono ?_),?_⟩
  · intro x hx
    obtain rfl := List.mem_singleton.mp hx
    exact List.mem_append_left _ (r_local K _ (by simp [jacCoords]))
  · intro hk
    have xx := it.val _ vx
    have zz := it.val _ vz
    simp only [Function.update_of_ne hxz,Function.update_self] at xx zz
    change tmv C K.M.n base t K.R.x=tmv C K.M.n base s K.R.x at xx
    change tmv C K.M.n base t K.R.z=tmv C K.M.n base s K.R.z*tmv C K.M.n base s K.R.z at zz
    rw [xx,zz]
    exact xOnly_of_jac hC (hI.result hk)

end VG.Proof.Ecdh.X86_64.Secret
