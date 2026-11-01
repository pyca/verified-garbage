module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConfig
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombHorner
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombEntry
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombAdd
import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! One signed comb digit advances the shared scalar-multiplication invariant. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm
open VG.Proof.Weierstrass.Arm.Point
open Spec.Weierstrass

structure Acc (K : TCombCfg) (C : Curve) (base : Addr) (k j : Nat) (s : State) : Prop where
  lt : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z], wordsVal s.mem base x K.L.M.n<C.p
  rep : Rep C (tmv C K.L.M.n base s K.L.R.x) (tmv C K.L.M.n base s K.L.R.y)
    (tmv C K.L.M.n base s K.L.R.z) (mul (combEW K.w k K.J j) (G C))

theorem step_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : Config K C tbl start) (hC : Law C) (hG : onCurve C (G C)=true)
    {s : State} {base T : Addr} {k j : Nat}
    (i : CurveInputs K C tbl base T k s) (acc : Acc K C base k j s)
    (hj : 1≤j) (hJ : j≤K.J) (hk : k<2^K.L.nbits) (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (hd : Region.Disjoint ⟨T,8*(tableWords K C tbl).length⟩ ⟨base,4096⟩) :
    WP isa K.step s fun t =>
      Rest powClob s t ∧ Unch base (loopWrites K) s.mem t.mem ∧
      CurveInputs K C tbl base T k t ∧ Acc K C base k (j-1) t ∧
      t.gpr .r11=BitVec.ofNat 32 (j-1) ∧ t.z=decide (j-1=0) := by
  apply WP.of_syms
  unfold TCombCfg.step
  have dec : WP isa (.block [decCounter]) s fun u =>
      u.gpr .r11=BitVec.ofNat 32 (j-1) ∧ RegOnly [.r11] s u :=
    wp_decCounter hj gj fun u up => WP.block_nil ⟨up.gpr,⟨up.rest (by simp),up.mem⟩⟩
  refine WP.seq (WP.mono_syms dec fun u ⟨gu,ku⟩ syu => ?_)
  have iu : CurveInputs K C tbl base T k u := i.keep h.layout h.bitsLow h.bitsHigh hd ku.keep
    (by decide) (by rw [ku.mem]; exact Unch.refl _ _ _) syu
  refine WP.seq (WP.mono_syms (entry_ok K h hC iu (by omega) hk gu hd)
    fun v ⟨kv,ov,rv,lv,pv⟩ syv => ?_)
  have iv : CurveInputs K C tbl base T k v := iu.keep h.layout h.bitsLow h.bitsHigh hd kv (by decide) ov syv
  have rlt : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z],wordsVal v.mem base x K.L.M.n<C.p := by
    intro x hx
    rw [rv x hx,ku.mem]
    exact acc.lt x hx
  have rrep : Rep C (tmv C K.L.M.n base v K.L.R.x) (tmv C K.L.M.n base v K.L.R.y)
      (tmv C K.L.M.n base v K.L.R.z) (mul (combEW K.w k K.J j) (G C)) := by
    show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [rv _ (by simp),rv _ (by simp),rv _ (by simp),ku.mem]
    exact acc.rep
  have hlt : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z,K.Q.x,K.Q.y,K.Q.z,
      Impl.Weierstrass.Point.aAt K.L.M.n,Impl.Weierstrass.Point.b3At K.L.M.n],
      wordsVal v.mem base x K.L.M.n<C.p := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    exact ⟨rlt _ (by simp),rlt _ (by simp),rlt _ (by simp),lv _ (by simp),lv _ (by simp),lv _ (by simp),
      iv.coeffA ▸ Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p)),
      iv.coeffB ▸ Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p))⟩
  refine WP.seq (WP.mono (add_ok K h.layout iv.scr iv.far h.fieldM h.fieldK h.modulus hlt)
    fun a ⟨ka,oa,la,ea⟩ => ?_)
  have ga : a.gpr .r11=BitVec.ofNat 32 (j-1) := by
    rw [ka.gpr .r11 (by decide),kv.gpr .r11 (by decide),gu]
  refine wp_testCounter (by have := h.J32; omega) ga fun t ft zt => WP.block_nil (fun syt => ?_)
  have keep : Rest powClob s t := (ku.keep.mono (by simp [powClob])).trans
    ((kv.mono (by simp [VG.Proof.Weierstrass.Arm.Mont.callClob,powClob,VG.Proof.Mont.Arm.clob])).trans
      ((ka.mono (by simp [powClob,VG.Proof.Mont.Arm.clob])).trans (ft.rest _)))
  have unch : Unch base (loopWrites K) s.mem t.mem := by
    rw [ft.mem]
    have ou : Unch base (loopWrites K) s.mem u.mem := by rw [ku.mem]; exact Unch.refl _ _ _
    exact (ou.trans (ov.trans oa)).cover fun w hw => ⟨w,by
      simpa only [List.mem_append,or_self] using hw,Nat.le_refl _,Nat.le_refl _⟩
  refine ⟨keep,unch,i.keep h.layout h.bitsLow h.bitsHigh hd keep (by decide) unch syt,
    ⟨by rw [ft.mem]; exact la,?_⟩,by rw [ft.gpr,ga],zt⟩
  have pa : Rep C (tmv C K.L.M.n base a K.L.R.x) (tmv C K.L.M.n base a K.L.R.y)
      (tmv C K.L.M.n base a K.L.R.z)
      (Spec.Weierstrass.add (mul (combEW K.w k K.J j) (G C)) (signedPtW C K.w k (j-1))) := by
    apply hC.add (hC.onCurve_mul hG _) (by
      unfold signedPtW combPtW
      split
      · exact hC.onCurve_mul hG _
      · exact onCurve_negPt (hC.onCurve_mul hG _)) rrep pv
    change _=(toM _ _ _,toM _ _ _,toM _ _ _)
    rw [ea]
    simp only [Eb,enc_9,enc_10]
    rw [iv.coeffA,iv.coeffB,toM_mont h.unit,toM_mont h.unit]
    simp only [rcbAddC,tmv,TCombCfg.Q,ptAt,enc_6,enc_7,enc_8,Bool.false_eq_true,↓reduceIte]
  have eqj : j-1+1=j := by omega
  have sum := combW_add hC hG (w := K.w) (k := k) (j := j-1) (J := K.J) (by omega)
  change Spec.Weierstrass.add _ (signedPtW C K.w k (j-1))=_ at sum
  rw [eqj] at sum
  rw [sum] at pa
  simpa only [tmv,ft.mem] using pa

end VG.Proof.Weierstrass.Arm.TComb
