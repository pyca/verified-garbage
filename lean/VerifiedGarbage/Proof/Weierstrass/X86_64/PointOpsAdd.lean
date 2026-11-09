module
public import VerifiedGarbage.Impl.Weierstrass.X86_64.PointOps
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacField
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState

import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Block
import Batteries.Logic
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract

/-!
# Point operations as functions on x86-64: what the cached addition computes

`addCachedBody`'s value: `R` becomes `jacAddCached` of the values of `R`,
`E` and `E`'s cached `Z²` and `Z³` at `sel`, whatever they are, through
its branches (`CachedJac.add`): `E` copied for `R`'s `Z = 0`, `R` for
`E`'s, else the header's `H` and `r`, then the doubling or the point at
infinity for `H = 0`, else the tail.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.PointOps

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Weierstrass.X86_64.CachedJac (headN rename rename_inj head_eq tail_eq slots out)

/-- What the cached addition's body needs of the slots: those of
`CachedJac.add`'s proofs, and that its programs read only `V` (`R`, `E`
and the cached powers) or what they wrote. -/
structure CachedLay (K : WinCfg) (sel size : Nat) (Sl : Nat → Prop) (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul) : Prop where
  lay : Lay K.M size Sl
  apart : RcbApart K.S K.R K.E K.D
  c2 : sel ∉ rcbW K.S K.D
  c3 : sel + 8 * K.M.n ∉ rcbW K.S K.D
  sl : ∀ x ∈ (rcbW K.S K.D ++ rcbR K.S K.R K.E) ++ [sel, sel + 8 * K.M.n], Sl x
  head : readsOk (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel)
    (jacCoords K.R ++ jacCoords K.E ++ [sel, sel + 8 * K.M.n]) = true
  tail : readsOk (jacTail K.S K.R K.E K.D) (validAfter
    (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel)
    (jacCoords K.R ++ jacCoords K.E ++ [sel, sel + 8 * K.M.n])) = true
  dbl : readsOk (dbl K.S K.R K.D) (jacCoords K.R) = true
  accum : (jacCoords K.R).Nodup
  copy : ∀ x ∈ jacCoords K.D, ∀ y ∈ jacCoords K.R, x ≠ y

section
variable {K : WinCfg} {sel : Nat} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
  {dbl : RcbSlots → Pt → Pt → List FOp}

/-- The values the cached addition reads. -/
abbrev cV (K : WinCfg) (sel : Nat) : List Nat := jacCoords K.R ++ jacCoords K.E ++ [sel, sel + 8 * K.M.n]

end

section
variable {K : WinCfg} {sel : Nat} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
  {dbl : RcbSlots → Pt → Pt → List FOp}

end
end VG.Proof.Weierstrass.X86_64.PointOps
