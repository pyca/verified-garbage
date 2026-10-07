import VerifiedGarbage.Proof.Weierstrass.X86_64.PointTransfer
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState

/-! A point copy with an exact field environment, including writes back to the accumulator. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem copyPointTransfer_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s)
    {o q : Pt} (hy : o.y=o.x+32) (hz : o.z=o.x+64)
    (hD : ∀ x∈jacCoords o,Sl x) (hQ : ∀ x∈jacCoords q,x∈V)
    (hap : ∀ x∈jacCoords q,∀ y∈jacCoords o,x≠y) :
    WP isa (.block (copyPt M.n o q)) s fun t =>
      ProgKeep M base (jacCoords o) s t ∧
      Inv M base size m Sl (jacCoords o++V) (pointTransferEnv E o q) t := by
  have hN : (jacCoords o).Nodup := by
    simp (disch := omega) [jacCoords,hy,hz]
  refine WP.mono (copyPointFields_ok hL hN hap hD hI hQ) fun t ⟨E',kt,it,he⟩ => ?_
  simp only [Prod.mk.injEq] at he
  refine ⟨kt,{it with val := ?_}⟩
  intro x hx
  simp only [pointTransferEnv]
  split
  · subst x
    exact (it.val _ hx).trans he.1
  · split
    · subst x
      exact (it.val _ hx).trans he.2.1
    · split
      · subst x
        exact (it.val _ hx).trans he.2.2
      · have hnot : x∉jacCoords o := by
          simp_all only [jacCoords,List.mem_cons,List.not_mem_nil,or_false,not_false_eq_true]
        have hv : x∈V := (List.mem_append.mp hx).resolve_left hnot
        rw [kt.slot hL hI.scr hD (hI.sl x hv) hnot,hI.val x hv]

end VG.Proof.Weierstrass.X86_64
