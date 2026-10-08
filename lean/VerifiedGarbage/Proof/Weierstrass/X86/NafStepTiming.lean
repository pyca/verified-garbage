import VerifiedGarbage.Proof.Weierstrass.X86.NafCounterTiming

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

structure NafStepChecks (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) : Prop where
  digit : NafDigitChecks K F
  double : ScratchCT (fprog F (dblJMul K.S K.R K.D))
  dec : RegCT [.esi] (.block [.alu .sub .esi (.imm 1)])
  test : RegCT [.esi] (.block [.alu .test .esi (.reg .esi)])

theorem nafStep_relCT {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk k j : Nat} {P : Point C}
    (hL : NafLay K size) (hJ : K.J=65) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p) (hj : j<256) (hP : onCurve C P=true)
    (hc : NafStepChecks K F) :
    RelCT isa (NafRunPair K C base size P (Naf5.byte k) (Naf5.residual k (j+1)) (BitVec.ofNat 32 (j+1)))
      (Naf.windowStep K F)
      (fun s t => NafRunPair K C base size P (Naf5.byte k) (Naf5.residual k j) (BitVec.ofNat 32 j) s t ∧
        s.zf=some (decide (j=0)) ∧ t.zf=some (decide (j=0))) := by
  have dec := nafRun_keeps_relCT (K:=K) (C:=C) (base:=base) (size:=size) (P:=P)
    (β:=Naf5.byte k) (e:=Naf5.residual k (j+1)) (counter:=BitVec.ofNat 32 (j+1))
    (counter':=BitVec.ofNat 32 j) (Post:=fun _ => True) (ws:=[.esi]) (by decide) hc.dec
    (fun _ ct => wp_decCounter (by omega) ct (fun _ cn kn mn => WP.block_nil
      ⟨by simpa only [Nat.add_sub_cancel] using cn,trivial,kn.1,mn,kn.2⟩))
  rw [Naf.windowStep]
  apply RelCT.seq (dec.mono (fun _ _ h => h) (fun _ _ h => h.1))
  apply RelCT.assoc
  apply RelCT.seq (nafDoubleCore_relCT hL hJ hW hBitsWk hm hC ha hP hc.double hc.digit.copy)
  apply RelCT.seq (nafDigit_relCT hL hJ hW hBitsWk hm hC ha hOne (by omega) hP hc.digit)
  exact nafRun_keeps_relCT (ws:=[]) (by simp) hc.test (fun _ ct =>
    wp_testCounter (by omega) ct (fun _ ft zt => WP.block_nil
      ⟨(congrFun ft.gpr .esi).trans ct,zt,(fun r _ => congrFun ft.gpr r),ft.mem,ft.rd,ft.wr⟩))

end VG.Proof.Weierstrass.X86
