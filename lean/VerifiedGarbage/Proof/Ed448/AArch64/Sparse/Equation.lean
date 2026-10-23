module

import VerifiedGarbage.Proof.Ed448.WnafWide.Group
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Spec
import VerifiedGarbage.Proof.Ed448.Group.Decode
public import VerifiedGarbage.Proof.Ed448.Group.Projective

/-! Relate the jointly computed point to the original cofactored RFC equation. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG
open VG.Proof.Ed448 (Rep dZ baseAff basePoint_rep pointMul_rep pointAdd_rep double_rep
  pointEqual_rep decodePoint_rep)
open VG.Proof.EdwardsLaw (EPoint)
open VG.Spec.Ed448 (Point)

theorem equation_eq {pk sig ch:List Byte} (hpk:pk.length=57) (hsig:sig.length=114)
    (hch:ch.length=57) {a r Q:Point} (ha:Spec.Ed448.decodePoint pk=some a)
    (hr:Spec.Ed448.decodePoint (sig.take 57)=some r)
    (hq:∀ aA:EPoint dZ,Rep a aA → Rep Q
      ((Spec.Ed448.decodeLE (sig.drop 57):Int) • baseAff+
        (Spec.Ed448.decodeLE ch:Int) • (-aA))) :
    Spec.Ed448.verifyEquation pk sig ch=
      (decide (Spec.Ed448.decodeLE (sig.drop 57)<Spec.Ed448.L) &&
        Spec.Ed448.pointEqual (VG.Proof.Ed448.double (VG.Proof.Ed448.double Q))
          (VG.Proof.Ed448.double (VG.Proof.Ed448.double r))) := by
  obtain ⟨aA,hA⟩:=decodePoint_rep ha
  obtain ⟨rA,hR⟩:=decodePoint_rep hr
  have hQ:=hq aA hA
  rw [natCast_zsmul,natCast_zsmul] at hQ
  have q4:=double_rep (double_rep hQ)
  have r4:=double_rep (double_rep hR)
  have s1:=pointMul_rep 4 (pointMul_rep (Spec.Ed448.decodeLE (sig.drop 57)) basePoint_rep)
  have s2:=pointAdd_rep (pointMul_rep 4 hR)
    (pointMul_rep 4 (pointMul_rep (Spec.Ed448.decodeLE ch) hA))
  unfold Spec.Ed448.verifyEquation
  simp only [hpk,hsig,hch,bne_self_eq_false,Bool.or_false,Bool.false_eq_true,↓reduceIte,ha,hr]
  refine congrArg (decide _ && ·) (Bool.eq_iff_iff.mpr ?_)
  rw [pointEqual_rep s1 s2,pointEqual_rep q4 r4,Window.four_iff]
  simp only [smul_neg,neg_neg]

end VG.Proof.Ed448.AArch64.Sparse
