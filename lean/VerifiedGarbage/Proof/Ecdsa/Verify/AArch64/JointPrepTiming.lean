import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointTable
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.ArithmeticTableChecks
import VerifiedGarbage.Proof.Weierstrass.AArch64.ArithmeticTableTiming

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 Spec.Weierstrass

theorem jointPrep_trace {base : Addr} :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ s.sp=t.sp ∧
      sv p256 base s U=sv p256 base t U ∧ sv p256 base s V=sv p256 base t V)
      jointPrepProgram (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨hs,ht,hsp,hu,hv⟩ es et
  cases es with | seq gs qs =>
    cases et with | seq gt qt =>
      have hg := (fastPrep_relCT P256Joint.cfg.G (Or.inr rfl)
        (by decide) (by decide) (by decide) (by decide) (by decide) jointGPrep_checks
        _ _ _ _ _ _ ⟨hs,ht,hsp,hu⟩ gs gt).1
      obtain ⟨_,_,xs,ps,ks,os⟩ := fastPrep_ok P256Joint.cfg.G (Or.inr rfl) hs
        (src:=p256.sl U) (by decide) (by decide) (by decide) (by decide) (by decide)
      obtain ⟨_,_,xt,pt,kt,ot⟩ := fastPrep_ok P256Joint.cfg.G (Or.inr rfl) ht
        (src:=p256.sl U) (by decide) (by decide) (by decide) (by decide) (by decide)
      obtain ⟨_,rfl⟩ := Exec.det gs xs
      obtain ⟨_,rfl⟩ := Exec.det gt xt
      have vs := os.wordsVal (d:=p256.sl V) (k:=4) (by decide) (by decide)
      have vt := ot.wordsVal (d:=p256.sl V) (k:=4) (by decide) (by decide)
      have hq := (fastPrep_relCT P256Joint.cfg.K (Or.inl rfl)
        (by decide) (by decide) (by decide) (by decide) (by decide) jointQPrep_checks
        _ _ _ _ _ _ ⟨ps.scr,pt.scr,ks.sp.trans (hsp.trans kt.sp.symm),vs.trans (hv.trans vt.symm)⟩ qs qt).1
      exact ⟨by rw [hg,hq],trivial⟩

theorem JointPrepPost.fields {base : Addr} {g : Reg → BitVec 64} {P : Point p256.C} {s t : State}
    (h : JointPrepPost base g P s t) :
    ∀ x∈winRo P256Joint.cfg.K,tmv p256.C 4 base t x=tmv p256.C 4 base s x := by
  intro x hx
  simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
  have e : ∀ i<45,tmv p256.C 4 base t (p256.sl i)=tmv p256.C 4 base s (p256.sl i) :=
    fun i hi => by change toM _ _ (sv p256 base t i)=toM _ _ (sv p256 base s i); rw [h.same i hi]
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [e AP (by decide),e BM (by decide),e ZERO (by decide),e VG.Impl.Ecdh.AArch64.PX (by decide),e VG.Impl.Ecdh.AArch64.PY (by decide),
    e ONEP (by decide)]

/-- Shared table values and the exact public scalar digits after preparation. -/
def JointTablePair (base : Addr) (P : Point p256.C) (u v : Nat) (a b s t : State) : Prop :=
  ∃ E,FieldPair P256Joint.cfg.K.M base size p256.C.p (·∈jointSlots P256Joint.cfg)
    (nafLive P256Joint.cfg.K) E s t ∧
  ∃ g₁ g₂ a' b', JointPrepPost base g₁ P a a' ∧ JointPrepPost base g₂ P b b' ∧
    JointTablePost base g₁ P u v a' s ∧ JointTablePost base g₂ P u v b' t

theorem jointPrepTable_relCT (certs : Forward.Arithmetic.Cases) (hc : CfgOk p256) (hC : Law p256.C)
    {base : Addr} {P : Point p256.C} {u v : Nat} {a b : State} (hP : onCurve p256.C P=true) :
    RelCT isa (fun s t => s=a ∧ t=b ∧ JacWinPublic p256 base P v s t ∧
      sv p256 base s U=u ∧ sv p256 base t U=u)
      (.seq jointPrepProgram (ArithmeticTable.table P256Joint.cfg.K))
      (JointTablePair base P u v a b) := by
  intro s t ts tt s' t' ⟨rfl,rfl,hp,us,ut⟩ es et
  obtain ⟨g₁,fs⟩ := hp.left.fixed
  obtain ⟨g₂,ft⟩ := hp.right.fixed
  cases es with | seq ps ws =>
    cases et with | seq pt wt =>
      have he := (jointPrep_trace _ _ _ _ _ _ ⟨hp.left.scr,hp.right.scr,hp.sp,
        us.trans ut.symm,hp.left.scalar.trans hp.right.scalar.symm⟩ ps pt).1
      obtain ⟨_,_,xs,is⟩ := jointPrepStage_ok hc hC hp.left.scr fs hp.left.px hp.left.py hp.left.rep
      obtain ⟨_,_,xt,it⟩ := jointPrepStage_ok hc hC hp.right.scr ft hp.right.px hp.right.py hp.right.rep
      obtain ⟨_,rfl⟩ := Exec.det ps xs
      obtain ⟨_,rfl⟩ := Exec.det pt xt
      have pair : FieldPair P256Joint.cfg.K.M base size p256.C.p (·∈jacWinSlots P256Joint.cfg.K)
          (winRo P256Joint.cfg.K) _ _ _ :=
        ⟨is.field,it.field.congr_env (fun x hx => (it.fields x hx).trans
          ((hp.fields x hx).symm.trans (is.fields x hx).symm)),is.keep.sp.trans (hp.sp.trans it.keep.sp.symm)⟩
      obtain ⟨hw,E,pair'⟩ := arithmeticTable_relCT certs (jacLay hc rfl) rfl (jacAligned p256 rfl)
        (unitMod_pow_two hc.p_odd _) (by decide) (by decide)
        (by change 2^(64*4)%p256.C.p<p256.C.p; exact Nat.mod_lt _ (by have := hc.p_ge; omega))
        arithmeticTable_checks nafWindow_checks.treeCopy _ _ _ _ _ _ pair ws wt
      obtain ⟨_,_,ys,js⟩ := jointTableStage_ok certs hc hC hP is
      obtain ⟨_,_,yt,jt⟩ := jointTableStage_ok certs hc hC hP it
      obtain ⟨_,rfl⟩ := Exec.det ws ys
      obtain ⟨_,rfl⟩ := Exec.det wt yt
      rw [us,hp.left.scalar] at js
      rw [ut,hp.right.scalar] at jt
      refine ⟨by rw [he,hw],E,?_,g₁,g₂,_,_,is,it,js,jt⟩
      exact ⟨⟨pair'.left.scr,pair'.left.mod,
        fun x hx => List.mem_append_left _ (List.mem_append_left _ (pair'.left.sl x hx)),pair'.left.lt,pair'.left.val⟩,
        ⟨pair'.right.scr,pair'.right.mod,
        fun x hx => List.mem_append_left _ (List.mem_append_left _ (pair'.right.sl x hx)),pair'.right.lt,pair'.right.val⟩,pair'.sp⟩

end VG.Proof.Ecdsa.Verify.AArch64
