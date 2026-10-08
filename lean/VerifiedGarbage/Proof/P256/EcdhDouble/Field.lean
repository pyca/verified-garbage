import VerifiedGarbage.Proof.P256.EcdhDouble.Raw
import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
import VerifiedGarbage.Proof.Weierstrass.JacInplace
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming

namespace VG.Proof.P256.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.P256.VerifyArithmetic Spec.Weierstrass
open EcdhJac (C K M Sl layout aligned live ro work)

theorem result_unch {F : Type _} [Lean.Grind.CommRing F] (E : Nat→F) {x : Nat}
    (hx : x∉writes) : result E x=E x := by
  simp only [writes,List.mem_cons,List.not_mem_nil,or_false,not_or] at hx
  simp [result,ops1,ops2,ops3,ops4,runOps,FOp.run,
    hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2.1,hx.2.2.2.2.2.1,
    hx.2.2.2.2.2.2.1,hx.2.2.2.2.2.2.2.1,hx.2.2.2.2.2.2.2.2]

theorem result_live {F : Type _} [Lean.Grind.CommRing F] (E : Nat→F) :
    ∀x∈live,result E x=runOps (operations .doubleRR) E x := by
  have e := (result_xyz E).trans (values_eq (E 512) (E 544) (E 576))
  have d := dblJMul_inplace_run (S:=K.S) (p:=K.R) (by decide +kernel) E
  change (runOps (operations .doubleRR) E 512,runOps (operations .doubleRR) E 544,
    runOps (operations .doubleRR) E 576)=dblJF (E 512) (E 544) (E 576) at d
  have ex := e.trans d.symm
  intro x hx
  change x∈[512,544,576]++ro at hx
  rcases List.mem_append.mp hx with hx|hx
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact congrArg Prod.fst ex
    · exact congrArg (fun p => p.2.1) ex
    · exact congrArg (fun p => p.2.2) ex
  · rw [result_unch E ((show ∀x∈ro,x∉writes by decide +kernel) x hx)]
    symm
    apply runOps_of_not_out
    exact (show ∀x∈ro,∀op∈operations .doubleRR,op.out≠x by decide +kernel) x hx

 theorem field_ok
    (h129 : LinearCorrect (Impl.P256.Linear.linear129 960 928 960) 960 928 960 12 9)
    (h38 : LinearCorrect (Impl.P256.Linear.linear38 544 896 800) 544 896 800 3 8)
    (hm : UnitMod C.p (2^256)) {base : Addr} {s : State} {E : Nat→Fe C}
    (hi : Inv M base 8192 C.p Sl live E s) :
    WP isa Impl.P256.EcdhDouble.program s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧
      Inv M base 8192 C.p Sl live (runOps (operations .doubleRR) E) t := by
  refine WP.mono (Certificate.refine hi.scr (raw_ok h129 h38 hm hi))
    fun t ⟨u,⟨_,hu⟩,ho,hk⟩ => ?_
  have hs := hk.scr allocatedRegs_x0 hi.scr
  have ht := hi.mod.unch hk.unch
    (show ∀w∈VerifyAllocated.work,M.mo+8*M.n≤w.1 ∨ w.1+w.2≤M.mo by decide)
    hi.scr.nowrap
  refine ⟨hk.mono (fun _ h => h) (by decide +kernel),?_⟩
  apply (hu.congr_env (result_live E)).of_observed hs ht
  intro x hx i him
  apply ho (x+8*i) ((show ∀x∈live,∀i<4,Certificate.observe (x+8*i) by decide +kernel) x hx i him)
  · have ha := aligned.sl x (hu.sl x hx)
    omega
  · have hb := layout.le x (hu.sl x hx)
    change i<4 at him
    change x+32≤8192 at hb
    omega

 theorem double_ok
    (h129 : LinearCorrect (Impl.P256.Linear.linear129 960 928 960) 960 928 960 12 9)
    (h38 : LinearCorrect (Impl.P256.Linear.linear38 544 896 800) 544 896 800 3 8)
    (hm : UnitMod C.p (2^256)) (hC : Law C) (ha : AM3 C)
    {base : Addr} {E : Nat→Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl live E s) {P : Point C}
    (hp : onCurve C P=true) (hj : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P) :
    WP isa Impl.P256.EcdhDouble.program s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧ Inv M base 8192 C.p Sl live (runOps (operations .doubleRR) E) t ∧
      InvJ C (runOps (operations .doubleRR) E K.R.x) (runOps (operations .doubleRR) E K.R.y)
        (runOps (operations .doubleRR) E K.R.z) (add P P) := by
  exact WP.mono (field_ok h129 h38 hm hi) fun _ ⟨hk,it⟩ =>
    ⟨hk,it,InvJ.dbl' hC ha hp hj (dblJMul_inplace_run (by decide +kernel) E)⟩
end VG.Proof.P256.EcdhDouble
