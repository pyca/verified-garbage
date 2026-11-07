module

import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoad
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Ladder
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem

/-! Field environments after multi-coordinate public table transfers. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont

/-- A multiple-slot update can reconstruct its environment from the resulting
memory. Bounds on changed slots and the frame preserve every initialized slot. -/
theorem Inv.of_progKeep {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) {V W : List Nat}
    {E : Nat → Fin m} {s t : State} (hI : Inv M base size m Sl V E s)
    (hk : ProgKeep M base W s t) (hW : ∀ x ∈ W, Sl x)
    (hlt : ∀ x ∈ W, wordsVal t.mem base x M.n < m) :
    Inv M base size m Sl (W++V)
      (fun x => toM m (2^(64*M.n)) (wordsVal t.mem base x M.n)) t := by
  have hn := hI.scr.nowrap
  have hm : ∀ w ∈ W.map (·,8*M.n) ++ [(M.tmp,8*M.n)],
      M.mo+8*M.n ≤ w.1 ∨ w.1+w.2 ≤ M.mo := by
    intro w hw
    simp only [List.mem_append,List.mem_map,List.mem_singleton] at hw
    rcases hw with ⟨x,hx,rfl⟩ | rfl
    · exact (hL.mo x (hW x hx)).symm
    · exact hI.mod.sep
  refine ⟨hk.scr hI.scr,hI.mod.unch hk.unch hm hn,?_,?_,fun _ _ => rfl⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hW x hx
    · exact hI.sl x hx
  · intro x hx
    by_cases hw : x ∈ W
    · exact hlt x hw
    · have hv : x ∈ V := (List.mem_append.mp hx).resolve_left hw
      have hb := hL.le x (hI.sl x hv)
      rw [hk.unch.wordsVal (fun w hw' => ?_) (by omega)]
      · exact hI.lt x hv
      · simp only [List.mem_append,List.mem_map,List.mem_singleton] at hw'
        rcases hw' with ⟨y,hy,rfl⟩ | rfl
        · exact hL.apart x y (hI.sl x hv) (hW y hy) (fun he => hw (he ▸ hy))
        · exact hL.tmp x (hI.sl x hv)

end VG.Proof.Weierstrass.AArch64
