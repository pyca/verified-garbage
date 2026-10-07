import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowNeg
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont

theorem negFieldWindow_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2^(64*M.n))) {V : List Nat} {E : Nat → Fin m}
    {neg z y w bits k j N : Nat}
    (hneg : Sl neg) (hz : z ∈ V) (hy : y ∈ V) (hny : neg ≠ y) (hzero : E z=0)
    (hw1 : 1 ≤ w) (hw : w<65536) (hj : w*j+w ≤ N)
    (hN : bits+N ≤ size) (hbw : bits+w-1<4096)
    (hbn : bits+N ≤ neg ∨ neg+8*M.n ≤ bits)
    (hbt : bits+N ≤ M.tmp ∨ M.tmp+8*M.n ≤ bits)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
      (.block (negYW M w neg z y bits))) :
    RelCT isa (fun s t => FieldPair M base size m Sl V E s t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      (∀ i<N, s.mem (off base (bits+i))=if k.testBit i then 1 else 0) ∧
      (∀ i<N, t.mem (off base (bits+i))=if k.testBit i then 1 else 0))
      (.block (negYW M w neg z y bits))
      (FieldPair M base size m Sl (y::neg::V)
        (Function.update (Function.update E neg (-E y)) y
          (if decide (combWin w k j < 2^(w-1)) then -E y else E y))) := by
  intro s t ts tt s' t' ⟨hp,ps,pt,bs,bt⟩ es et
  obtain ⟨_,_,xs,ks,is⟩ := negFieldWindow_ok hL hAl hm hp.left hneg hz hy hny hzero
    hw1 hw hj hN hbw ps bs hbn hbt
  obtain ⟨_,_,xt,kt,it⟩ := negFieldWindow_ok hL hAl hm hp.right hneg hz hy hny hzero
    hw1 hw hj hN hbw pt bt hbn hbt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  have pub : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]) s t := by
    refine ⟨hp.sp,fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
    · exact ps.trans pt.symm
  exact ⟨hct _ _ _ _ _ _ trivial trivial pub es et,is,it,ks.sp.trans (hp.sp.trans kt.sp.symm)⟩

end VG.Proof.Weierstrass.AArch64
