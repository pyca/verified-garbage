import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableInit
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableStep

/-! The complete public loop constructs sixteen peer multiples with cached powers. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem table_loop_ok {K : WinCfg} {base : Addr} {size : Nat}
    (hL : SecretLay K size) (hm : UnitMod Spec.P256.p (2^(64*K.M.n)))
    (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve) (hO : PeerOrder Spec.P256.curve)
    (ht : K.tbl<2^31) {P : Point Spec.P256.curve}
    (hP : onCurve Spec.P256.curve P=true) (hne : P≠.infinity)
    {s₀ s : State} (hI : TableInv K Spec.P256.curve base size P s₀ s 1) :
    WP isa (.loop (Impl.Ecdh.X86_64.Window5.tableStep K) .ne) s fun t =>
      TableInv K Spec.P256.curve base size P s₀ t 16 := by
  let I := fun r t => 1≤r ∧ r≤15 ∧ TableInv K Spec.P256.curve base size P s₀ t (16-r)
  have hi : I 15 s := ⟨by decide,by decide,hI⟩
  refine WP.loop (M:=isa) I (fun r u ⟨hr1,hr15,iu⟩ => ?_) 15 s hi
  refine WP.mono (table_step_ok hL hm hC ha hO (by omega) (by omega) ht hP hne iu)
    fun t ⟨it,zt⟩ => ?_
  by_cases he : r=1
  · subst r
    refine Or.inl ⟨?_,it⟩
    change t.zf.map (!·)=some false
    rw [zt]
    rfl
  · refine Or.inr ⟨?_,r-1,by omega,by omega,by omega,?_⟩
    · change t.zf.map (!·)=some true
      rw [zt]
      simp only [show ¬(16-r+1=16) by omega,decide_false,Option.map_some,Bool.not_false]
    · simpa only [show 16-(r-1)=16-r+1 by omega] using it

theorem table_build_ok {K : WinCfg} {base : Addr} {size : Nat}
    (hL : SecretLay K size) (hm : UnitMod Spec.P256.p (2^(64*K.M.n)))
    (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve) (hO : PeerOrder Spec.P256.curve)
    (ht : K.tbl<2^31) (hOne : K.one<Spec.P256.p)
    (hOneVal : toM Spec.P256.p (2^(64*K.M.n)) K.one=1)
    {P : Point Spec.P256.curve} (hP : onCurve Spec.P256.curve P=true) (hne : P≠.infinity)
    {s : State} {E : Nat → Fin Spec.P256.p}
    (hI : Inv K.M base size Spec.P256.p (·∈slots K) (winRo K) E s)
    (hJ : InvJ Spec.P256.curve (E K.P.x) (E K.P.y) (E K.P.z) P) (hAff : E K.P.z=1) :
    WP isa (Impl.Ecdh.X86_64.Window5.build K) s fun t =>
      TableInv K Spec.P256.curve base size P s t 16 := by
  rw [Impl.Ecdh.X86_64.Window5.build]
  apply WP.seq
  exact WP.mono (table_init_ok (C:=Spec.P256.curve) hL hOne hOneVal hI hJ hAff)
    (fun _ hi => table_loop_ok hL hm hC ha hO ht hP hne hi)

end VG.Proof.Ecdh.X86_64.Secret
