import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheEntryPoint
import VerifiedGarbage.Proof.Weierstrass.FastNaf

/-! The cached peer lookup represents a nonzero width-five digit of the joint sum. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

theorem jointCachedFast_ok {K : WinCfg} {s : State} {base : Addr} {size tbl dst u j : Nat}
    {C : Curve} {P : Point C}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C}
    (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hi : Inv K.M base size C.p Sl V E s)
    (hmag : FastNaf.magnitude 5 u j≠0)
    (h8 : s.gpr .r8=(FastNaf.byte 5 u j).setWidth 64)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hp : K.tbl<2^31) (hc : tbl<2^31)
    (hP : K.tbl+192*K.M.n≤size) (hC : tbl+128*K.M.n≤size)
    (hD : ∀ x∈cachedSlots K.M.n K.E dst,Sl x)
    (hQ : ∀ x∈cachedSlots K.M.n (K.tblPt ((FastNaf.magnitude 5 u j-1)/2+1))
      (tbl+16*K.M.n*((FastNaf.magnitude 5 u j-1)/2)),x∈V)
    (hEP : K.E.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.E.x)
    (hEC : K.E.x+24*K.M.n≤tbl ∨ tbl+128*K.M.n≤K.E.x)
    (hDC : dst+16*K.M.n≤tbl ∨ tbl+128*K.M.n≤dst)
    (hDE : dst+16*K.M.n≤K.E.x ∨ K.E.x+24*K.M.n≤dst)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hApart : K.zero∉cachedSlots K.M.n K.E dst)
    (hPoint : CachedPoint K.M.n C E (K.tblPt ((FastNaf.magnitude 5 u j-1)/2+1))
      (tbl+16*K.M.n*((FastNaf.magnitude 5 u j-1)/2)) (mul (FastNaf.magnitude 5 u j) P)) :
    WP isa (Naf.signedCachedEntry K tbl dst) s fun t =>
      ProgKeep K.M base (cachedSlots K.M.n K.E dst) s t ∧
      Inv K.M base size C.p Sl (cachedSlots K.M.n K.E dst++V)
        (cachedEntryEnv K E tbl dst (FastNaf.byte 5 u j)) t ∧
      CachedPoint K.M.n C (cachedEntryEnv K E tbl dst (FastNaf.byte 5 u j)) K.E dst
        (FastNaf.point C P 5 u j) := by
  have he : nafMagnitude (FastNaf.byte 5 u j)=FastNaf.magnitude 5 u j := FastNaf.byte_magnitude 5 u j
  have ha : 1≤nafMagnitude (FastNaf.byte 5 u j) := by rw [he]; omega
  have ha' : nafMagnitude (FastNaf.byte 5 u j)≤15 := by
    rw [he]
    exact FastNaf.magnitude_le (Or.inl rfl) u j
  have hodd : nafMagnitude (FastNaf.byte 5 u j)%2=1 := by
    rw [he]
    exact (FastNaf.magnitude_odd_or_zero 5 u j).resolve_left hmag
  refine WP.mono (nafSignedCachedFields_ok hL hn hm hi ha ha' hodd h8 hy hz hp hc hP hC
    hD (by rw [he]; exact hQ) hEP hEC hDC hDE hZero heZero hApart) fun t ⟨kt,it⟩ => ?_
  have hpoint := cachedEntryEnv_point (E:=E) (b:=FastNaf.byte 5 u j) (by omega) hy hz hDE
    (by rw [he]; exact hPoint)
  have ep : (if (FastNaf.byte 5 u j).toNat<128 then mul (FastNaf.magnitude 5 u j) P
      else negPt (mul (FastNaf.magnitude 5 u j) P))=FastNaf.point C P 5 u j := by
    rw [FastNaf.point,←FastNaf.byte_negative]
    by_cases h : (FastNaf.byte 5 u j).toNat<128
    · simp only [h,ite_true,show ¬128≤(FastNaf.byte 5 u j).toNat from by omega,decide_false,ite_false,Bool.false_eq_true]
    · simp only [h,ite_false,show 128≤(FastNaf.byte 5 u j).toNat from by omega,decide_true,ite_true]
  rw [ep] at hpoint
  exact ⟨kt,it,hpoint⟩

end VG.Proof.Weierstrass.X86_64
