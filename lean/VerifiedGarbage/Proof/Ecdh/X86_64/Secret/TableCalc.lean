import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.LayoutOps
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Double
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Mixed
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableIndex
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointCopy
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointMask

/-! Compute the next table point by doubling its half-index or adding the peer. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem table_calc_ok {K : WinCfg} {base : Addr} {size j : Nat}
    (hL : SecretLay K size) (hm : UnitMod Spec.P256.p (2^(64*K.M.n)))
    (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve) (hO : PeerOrder Spec.P256.curve)
    (hj2 : 2≤j) (hj16 : j≤16)
    {V : List Nat} {E : Nat → Fin Spec.P256.p} {s : State}
    (hI : Inv K.M base size Spec.P256.p (·∈slots K) V E s)
    (hV : ∀ x∈rcbR K.S K.R K.P,x∈V)
    (hz : s.zf=some (decide (j%2=0))) {P : Point Spec.P256.curve}
    (hP : onCurve Spec.P256.curve P=true) (hne : P≠.infinity)
    (hJP : InvJ Spec.P256.curve (E K.R.x) (E K.R.y) (E K.R.z) (mul (tableParent j) P))
    (hJQ : InvJ Spec.P256.curve (E K.P.x) (E K.P.y) (E K.P.z) P) (hAff : E K.P.z=1) :
    WP isa (Impl.Ecdh.X86_64.Window5.tableCalc K) s fun t =>
      ∃ F, ProgKeep K.M base (localWrites K) s t ∧
      Inv K.M base size Spec.P256.p (·∈slots K) V F t ∧
      InvJ Spec.P256.curve (F K.R.x) (F K.R.y) (F K.R.z) (mul j P) := by
  have hvr : ∀ x∈[K.R.x,K.R.y,K.R.z],x∈V := by
    intro x hx
    apply hV x
    simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  rw [Impl.Ecdh.X86_64.Window5.tableCalc]
  refine WP.ite (decide (j%2=0)) hz (fun he => ?_) (fun he => ?_)
  · have hj := of_decide_eq_true he
    refine WP.mono (dbl_self_ok hL.n hL.lay hm hC ha hL.double_nodup
      (fun x hx => local_slots K x (double_local K x hx)) hI hvr
      (valid:=True) (fun _ => hC.onCurve_mul hP _) (fun _ => hJP)) fun t ⟨kt,it,jt⟩ => ?_
    have hp := jt trivial
    have hi : tableParent j+tableParent j=j := by simp only [tableParent,hj,ite_true]; omega
    rw [hC.add_mul_mul hP,hi] at hp
    exact ⟨_,kt.mono (double_local K),it,hp⟩
  · have hj := of_decide_eq_false he
    have hi : 1<tableParent j := by simp only [tableParent,hj,ite_false]; omega
    have hin : tableParent j+1<Spec.P256.curve.n := by
      simp only [tableParent,hj,ite_false]
      exact Nat.lt_of_le_of_lt (by omega : j-1+1≤16) (by decide)
    have hsl : ∀ x∈rcbW K.S K.D++rcbR K.S K.R K.P,x∈slots K := by
      intro x hx
      rcases List.mem_append.mp hx with hx|hx
      · exact local_slots K x (rcb_local K x hx)
      · exact hI.sl x (hV x hx)
    apply WP.seq
    refine WP.mono (table_mixed_ok hL.n hL.lay hm hC ha hO hL.rcbApart_RP hsl
      hI hV hP hne hi hin hJP hJQ hAff) fun u ⟨F,ku,iu,ju⟩ => ?_
    rw [←hL.n]
    refine WP.mono (copyPointTransfer_ok hL.lay iu hL.rxy hL.rxz
      (fun x hx => local_slots K x (r_local K x hx))
      (fun _ hx => List.mem_append_left _ hx) hL.copy_DR) fun t ⟨kt,it⟩ => ?_
    have hv := pointTransferEnv_values F K.R K.D hL.rxy hL.rxz
    simp only [Prod.mk.injEq] at hv
    have hi' : tableParent j+1=j := by simp only [tableParent,hj,ite_false]; omega
    refine ⟨_,(ku.mono (rcb_local K)).trans (kt.mono (r_local K)),
      it.sub (fun _ hx => List.mem_append_right _ (List.mem_append_right _ hx)),?_⟩
    rw [hv.1,hv.2.1,hv.2.2,←hi']
    exact ju

end VG.Proof.Ecdh.X86_64.Secret
