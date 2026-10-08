import VerifiedGarbage.Proof.P256.EcdhJac.BuildDblu
import VerifiedGarbage.Proof.P256.EcdhJac.Zaddu
import VerifiedGarbage.Proof.P256.EcdhJac.Counter

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem CoZInv.keeps {base : Addr} {P : Point C} {k m : Nat} {s t : State}
    {rs : List Reg} (hi : CoZInv base P k m s) (hk : Keeps rs s t)
    (hr : rs⊆regs) (hc : t.gpr .x19=BitVec.ofNat 64 m) : CoZInv base P k m t := by
  refine ⟨⟨hi.inv.fixed.keep (frame_build ((AllocatedFrame.of_keeps hk).widenRegs hr)),?_,
    selected_keeps hi.inv.selected hk,hc⟩,?_,?_⟩
  · intro a ha ham; apply (hi.inv.table a ha ham).congr; intro i hi; rw [hk.mem]
  · simpa only [hk.mem] using hi.lt
  · simpa only [tmv,hk.mem] using hi.d

theorem buildIncrement_ok (s : State) {m : Nat} (hc : s.gpr .x19=BitVec.ofNat 64 m) :
    WP isa (.block [.addImm .x .x19 .x19 1]) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 (m+1) ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 1<4096 by decide,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,
    hc,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  · exact BitVec.ofNat_add_ofNat _ _
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

theorem buildTest_ok (s : State) :
    WP isa (.block [.subImm .x .x4 .x19 16]) s fun t =>
      t.gpr .x4=s.gpr .x19-16 ∧ Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 16<4096 by decide,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,
    Option.some.injEq,exists_eq_left']
  refine ⟨rfl,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write,hr,ite_false]

theorem buildStep_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k m : Nat} {s : State} (hP : onCurve C P=true)
    (hm2 : 2≤m) (hm15 : m≤15) (hi : CoZInv base P k m s) :
    WP isa Impl.P256.EcdhJac.buildStep s fun t =>
      Frame base buildWork s t ∧ CoZInv base P k (m+1) t ∧
      t.gpr .x4=BitVec.ofNat 64 (m+1)-16 := by
  unfold Impl.P256.EcdhJac.buildStep
  refine WP.seq (WP.mono (buildIncrement_ok s hi.inv.counter) fun a ⟨ca,ka⟩ => ?_)
  have fa := hi.inv.fixed.keep (frame_build ((AllocatedFrame.of_keeps ka).widenRegs (by decide)))
  have pa := selected_keeps hi.inv.selected ka
  have la : ∀x∈[K.D.x,K.D.y],wordsVal a.mem base x 4<C.p := by simpa only [ka.mem] using hi.lt
  have da : InvJ C (tmv C 4 base a K.D.x) (tmv C 4 base a K.D.y) (tmv C 4 base a K.E.z) P := by
    simpa only [tmv,ka.mem] using hi.d
  refine WP.seq (WP.mono (zaddu_ok hC ha hO hP hm2 hm15 fa pa la da) fun b ⟨kb,fb,pb,lb,db,cb⟩ => ?_)
  have ta : TblOk base P m a := by
    intro j hj hjm; apply (hi.inv.table j hj hjm).congr; intro i hi; rw [ka.mem]
  have tb := table_keep ta (by omega) kb
  rw [WP.block_append_iff]
  refine WP.mono (storeCoZ_ok (m:=m+1) (by omega) (by omega) fb (by simpa using tb) pb lb db (cb.trans ca)) fun d ⟨kd,id⟩ => ?_
  refine WP.mono (buildTest_ok d) fun t ⟨ct,kt⟩ => ?_
  refine ⟨(frame_build ((AllocatedFrame.of_keeps ka).widenRegs (by decide))).trans
    ((frame_build kb).trans (kd.trans ((AllocatedFrame.of_keeps kt).widenRegs (by decide)))),
    id.keeps kt (by decide) ?_,ct.trans ?_⟩
  · rw [kt.gpr .x19 (by decide),id.inv.counter]
  · rw [id.inv.counter]
end VG.Proof.P256.EcdhJac
