import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourScalarLoad

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Sample (rbTry)

abbrev ScalarConsts := VG.Proof.MlDsa.AArch64.Sample.RejBounded.Consts

def scalarPairRegs : List Reg := [.x3,.x4,.x7,.x8,.x12,.x13,.x14]
def scalarPair (η : Nat) : Prog isa :=
 .ite (.zero .x .x4) (.block [])
   (.seq (.block (rbTry η++[.lsr .x .x7 .x6 4]))
     (.ite (.zero .x .x4) (.block []) (.block (rbTry η))))

theorem remaining_zero {s : State} {L : List Zq}
    (h4 : (s.gpr .x4).toNat=256-L.length) (hL : L.length≤256) :
    isa.eval (.zero .x .x4) s=some (decide (L.length=256)) := by
  rw [eval_zero,eq_zero_iff,h4]
  congr 1
  exact decide_eq_decide.mpr (by omega)

structure ScalarPairPost (η : Nat) (s t : State) (p : Addr) (L : List Zq) (b : Byte) : Prop where
 keep : Keep scalarPairRegs s t
 frame : Frame [polyR p] s.mem t.mem
 output : t.gpr .x3=coeffAddr p (rbStep η L b).length
 remaining : (t.gpr .x4).toNat=256-(rbStep η L b).length
 stored : Stored t.mem p (rbStep η L b)

theorem scalarPair_ok {η : Nat} (hη : η=2∨η=4) {s : State} {p : Addr} {L : List Zq} {b : Byte}
    (hC : ScalarConsts η s) (hL : L.length≤256) (hS : Stored s.mem p L)
    (h3 : s.gpr .x3=coeffAddr p L.length) (h4 : (s.gpr .x4).toNat=256-L.length)
    (h6 : s.gpr .x6=b.setWidth 64) (h7 : s.gpr .x7=BitVec.ofNat 64 (b.toNat%16))
    (hW : ∀j<256,InRegions s.wr (coeffAddr p j) 4) :
    WP isa (scalarPair η) s fun t=>ScalarPairPost η s t p L b := by
  unfold scalarPair
  by_cases hfull : L.length=256
  · have he : rbStep η L b=L:=by simp only [rbStep,n,hfull,Nat.lt_irrefl,ite_false]
    refine WP.ite true (by rw [remaining_zero h4 hL,decide_eq_true hfull])
      (fun _=>WP.block_nil_iff.mpr ?_) (fun h=>nomatch h)
    exact ⟨Keep.refl _ _,Frame.refl _ _,by rwa [he],by rwa [he],by rwa [he]⟩
  · refine WP.ite false (by rw [remaining_zero h4 hL,decide_eq_false hfull]) (fun h=>nomatch h) fun _=>?_
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.try_ok hη
      (by omega) hC h7 h3 h4 (by omega) hS (hW _ (by omega)))
      fun a ⟨hak,haf,ha3,ha4,has⟩=>?_
    refine WP.mono (scalarHigh_ok (s := a) (b := b) (by rw [hak.gpr .x6 (by decide)]; exact h6))
      fun c ⟨hck,hc7⟩=>?_
    let L1:=hbTry η L (b.toNat%16)
    have hL1 : L1.length≤256:=by
      have hh:=hbTry_length η L (b.toNat%16)
      have hb:=halfByteOk_le η (b.toNat%16)
      dsimp only [L1]; omega
    have hc4 : (c.gpr .x4).toNat=256-L1.length:=by rw [hck.get .x4]; exact ha4
    have hcs : Stored c.mem p L1:=by rw [hck.mem]; exact has
    have hcf : Frame [polyR p] s.mem c.mem:=by rw [hck.mem]; exact haf
    have hkeep : Keep scalarPairRegs s c:=(hak.trans hck.keep).mono (by decide)
    by_cases hfull1 : L1.length=256
    · have he : rbStep η L b=L1:=by
        simp only [rbStep,n,ifT (by omega : L.length<256)]
        rw [ifF (by change ¬L1.length<256; omega)]
      refine WP.ite true (by rw [remaining_zero hc4 hL1,decide_eq_true hfull1])
        (fun _=>WP.block_nil_iff.mpr ?_) (fun h=>nomatch h)
      exact ⟨hkeep,hcf,by rw [he,hck.get .x3]; exact ha3,by rwa [he],by rwa [he]⟩
    · have he : rbStep η L b=hbTry η L1 (b.toNat/16):=by
        simp only [rbStep,n,ifT (by omega : L.length<256)]
        rw [ifT (by change L1.length<256; omega)]
      refine WP.ite false (by rw [remaining_zero hc4 hL1,decide_eq_false hfull1]) (fun h=>nomatch h) fun _=>?_
      refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.try_ok hη
        (by have:=b.isLt; omega) (hC.keep hkeep (by decide)) hc7
        (by rw [hck.get .x3]; exact ha3) hc4 (by omega) hcs
        (by rw [hkeep.wr]; exact hW _ (by omega))) fun t ⟨htk,htf,ht3,ht4,hts⟩=>?_
      exact ⟨(hkeep.trans htk).mono (by decide),hcf.trans htf,by rwa [he],by rwa [he],by rwa [he]⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
