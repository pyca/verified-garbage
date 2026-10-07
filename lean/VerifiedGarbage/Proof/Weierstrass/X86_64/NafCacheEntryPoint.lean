import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheEntryFields
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheNeg

/-! The exact lookup environment preserves the point and its cached powers. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

theorem cachedTransferEnv_point {C : Curve} {E : Nat → Fe C} {o q : Pt} {dst src : Nat}
    (hy : o.y=o.x+32) (hz : o.z=o.x+64)
    (hDE : dst+64≤o.x ∨ o.x+96≤dst) {P : Point C}
    (hP : CachedPoint C E q src P) :
    CachedPoint C (cachedTransferEnv E o q dst src) o dst P := by
  have hyx : o.y≠o.x := by omega
  have hzx : o.z≠o.x := by omega
  have hzy : o.z≠o.y := by omega
  have hd : dst≠o.x ∧ dst≠o.y ∧ dst≠o.z := by omega
  have hd' : dst+32≠o.x ∧ dst+32≠o.y ∧ dst+32≠o.z ∧ dst+32≠dst := by omega
  simpa only [CachedPoint,cachedTransferEnv,hyx,hzx,hzy,hd.1,hd.2.1,hd.2.2,
    hd'.1,hd'.2.1,hd'.2.2.1,hd'.2.2.2,ite_false,ite_true] using hP

theorem cachedEntryEnv_point {K : WinCfg} {C : Curve} {E : Nat → Fe C} {tbl dst : Nat}
    {b : BitVec 8} (hy : K.E.y=K.E.x+32) (hz : K.E.z=K.E.x+64)
    (hDE : dst+64≤K.E.x ∨ K.E.x+96≤dst) {P : Point C}
    (hP : CachedPoint C E (K.tblPt ((nafMagnitude b-1)/2+1))
      (tbl+64*((nafMagnitude b-1)/2)) P) :
    CachedPoint C (cachedEntryEnv K E tbl dst b) K.E dst
      (if b.toNat<128 then P else negPt P) := by
  have h := cachedTransferEnv_point hy hz hDE hP
  have hxy : K.E.x≠K.E.y := by omega
  have hzy : K.E.z≠K.E.y := by omega
  have hd : dst≠K.E.y := by omega
  have hd' : dst+32≠K.E.y := by omega
  unfold cachedEntryEnv
  split
  · exact h
  · simp only [CachedPoint,Function.update_self,Function.update_of_ne hxy,
      Function.update_of_ne hzy,Function.update_of_ne hd,Function.update_of_ne hd']
    exact ⟨h.1.negY,h.2⟩

end VG.Proof.Weierstrass.X86_64
