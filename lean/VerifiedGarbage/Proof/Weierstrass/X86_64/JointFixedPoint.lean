import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedEntry
import VerifiedGarbage.Proof.Weierstrass.FastNaf

/-! The signed lookup represents the width-seven generator digit used in the joint sum. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

theorem jointFixedFast_ok {K : WinCfg} {s : State} {base T : Addr} {size x y u j : Nat}
    {C : Curve} {G : Point C} {tsym : String} {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C}
    (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hi : Inv K.M base size C.p Sl V E s) (hmag : FastNaf.magnitude 7 u j≠0)
    (h8 : s.gpr .r8=(FastNaf.byte 7 u j).setWidth 64)
    (hS : FixedSource K.M.n base T tsym size (FastNaf.magnitude 7 u j) x y s)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hD : ∀ v∈jacCoords K.E,Sl v) (hx : x<C.p) (hyy : y<C.p) (hOne : K.one<C.p)
    (hOneVal : toM C.p (2^(64*K.M.n)) K.one=1)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hApart : K.zero∉jacCoords K.E)
    (hPoint : InvJ C (toM C.p (2^(64*K.M.n)) x) (toM C.p (2^(64*K.M.n)) y) 1 (mul (FastNaf.magnitude 7 u j) G)) :
    WP isa (Joint.fixedEntry K tsym) s fun t =>
      ProgKeep K.M base (jacCoords K.E) s t ∧
      Inv K.M base size C.p Sl (jacCoords K.E++V) (fixedEntryEnv K C.p E (FastNaf.byte 7 u j) x y) t ∧
      InvJ C (fixedEntryEnv K C.p E (FastNaf.byte 7 u j) x y K.E.x)
        (fixedEntryEnv K C.p E (FastNaf.byte 7 u j) x y K.E.y)
        (fixedEntryEnv K C.p E (FastNaf.byte 7 u j) x y K.E.z) (FastNaf.point C G 7 u j) ∧
      fixedEntryEnv K C.p E (FastNaf.byte 7 u j) x y K.E.z=1 := by
  have he : nafMagnitude (FastNaf.byte 7 u j)=FastNaf.magnitude 7 u j := FastNaf.byte_magnitude 7 u j
  refine WP.mono (jointFixedEntry_fields_ok hL hn hm hi (by rw [he]; omega) h8
    (by rw [he]; exact hS) hy hz hD hx hyy hOne hZero heZero hApart) fun t ⟨kt,it⟩ => ?_
  have hp := fixedEntryEnv_point (E:=E) (b:=FastNaf.byte 7 u j) (by omega) hy hz hOneVal hPoint
  have ep : (if (FastNaf.byte 7 u j).toNat<128 then mul (FastNaf.magnitude 7 u j) G
      else negPt (mul (FastNaf.magnitude 7 u j) G))=FastNaf.point C G 7 u j := by
    rw [FastNaf.point,←FastNaf.byte_negative]
    by_cases h : (FastNaf.byte 7 u j).toNat<128
    · simp only [h,ite_true,show ¬128≤(FastNaf.byte 7 u j).toNat from by omega,decide_false,ite_false,Bool.false_eq_true]
    · simp only [h,ite_false,show 128≤(FastNaf.byte 7 u j).toNat from by omega,decide_true,ite_true]
  rw [ep] at hp
  exact ⟨kt,it,hp⟩

end VG.Proof.Weierstrass.X86_64
