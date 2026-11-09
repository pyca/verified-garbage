module
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLayout
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Jac

import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-! Store the new table multiple and advance the public loop counters. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

def jacCoords (p : Pt) : List Nat := [p.x,p.y,p.z]

theorem ProgKeep.slot {M : Mod} {base : Addr} {size : Nat} {Sl : Nat → Prop}
    {s t : State} {W : List Nat} (hL : Lay M size Sl) (hs : Scr s base size)
    (hk : ProgKeep M base W s t) (hW : ∀ x∈W, Sl x) {x : Nat}
    (hx : Sl x) (hn : x∉W) : wordsVal t.mem base x M.n=wordsVal s.mem base x M.n := by
  apply hk.unch.wordsVal _ (by have := hL.le x hx; have := hs.nowrap; omega)
  intro w hw
  simp only [List.mem_append,List.mem_map,List.mem_singleton] at hw
  rcases hw with ⟨y,hy,rfl⟩ | rfl
  · exact hL.apart x y hx (hW y hy) (fun he => hn (he ▸ hy))
  · exact hL.tmp x hx

end VG.Proof.Weierstrass.AArch64
