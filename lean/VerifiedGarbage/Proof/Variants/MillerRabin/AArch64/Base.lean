module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
public import VerifiedGarbage.Proof.Bignum.AArch64.MulFixedCallMont
import Mathlib.Tactic.SplitIfs

/-!
# The baseline shared round: the variant's code and proofs

The variant `VG.Variants.MillerRabin.AArch64.Base.variant`
(`Variants/MillerRabin/AArch64/Base.lean`), with the proofs its interface asks
for.
-/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.AArch64.Base

open VG.Proof.MillerRabin.AArch64 VG.Proof.Bignum.AArch64

/-- The shared squares and the baseline products have no frames. -/
theorem squareEightCall_noFrames (o a b : Nat) :
    (VG.Impl.Bignum.AArch64.SquareEightCall.mm o a b).noFrames = true := by
  simp only [VG.Impl.Bignum.AArch64.SquareEightCall.mm, VG.Impl.Bignum.AArch64.SquareCall.mm,
    VG.Impl.Bignum.AArch64.SquareCall.call, VG.Impl.Bignum.AArch64.BlockedRedc.mm,
    VG.Impl.Bignum.AArch64.Square.montMul]
  split_ifs with h1 <;> first
    | rfl
    | (obtain ⟨rfl, rfl, rfl⟩ := h1; decide +kernel)

/-- The Montgomery multiplication never touches PSTATE.DIT, for any arrays: its
long pieces do not depend on them (each decided once), and the instructions
that name the arrays are few. -/
theorem squareEightCall_noDit (o a b : Nat) :
    (VG.Impl.Bignum.AArch64.SquareEightCall.mm o a b).all (fun i => !i.touchesDit) = true := by
  have h1 : (VG.Impl.Bignum.AArch64.Square.cross).all (fun i => !i.touchesDit) = true := by lit_decide
  have h2 : (VG.Impl.Bignum.AArch64.Square.diagonal).all (fun i => !i.touchesDit) = true := by lit_decide
  have h3 : (VG.Impl.Bignum.AArch64.Square.redc).all (fun i => !i.touchesDit) = true := by lit_decide
  have h4 : (VG.Impl.Bignum.AArch64.BlockedRedc.redc).all (fun i => !i.touchesDit) = true := by lit_decide
  have h5 : (VG.Impl.Bignum.AArch64.subMod).all (fun i => !i.touchesDit) = true := by lit_decide
  have h6 : (VG.Impl.Bignum.AArch64.selectAcc).all (fun i => !i.touchesDit) = true := by lit_decide
  have h7 : (VG.Impl.Bignum.AArch64.zeroAcc).all (fun i => !i.touchesDit) = true := by lit_decide
  have h8 : (VG.Impl.Bignum.AArch64.rounds).all (fun i => !i.touchesDit) = true := by lit_decide
  have h9 : (VG.Impl.Bignum.AArch64.SquareEightDispatch.mm 6 6 6).all (fun i => !i.touchesDit) = true := by
    lit_decide
  simp only [VG.Impl.Bignum.AArch64.SquareEightCall.mm, VG.Impl.Bignum.AArch64.SquareCall.mm,
    VG.Impl.Bignum.AArch64.BlockedRedc.mm, VG.Impl.Bignum.AArch64.Square.montMul]
  split_ifs with hx hy hz hw <;>
  simp only [VG.Impl.Bignum.AArch64.SquareCall.call, VG.Impl.Bignum.AArch64.BlockedRedc.square,
    VG.Impl.Bignum.AArch64.Square.square, VG.Impl.Bignum.AArch64.Square.rawSquare,
    VG.Impl.Bignum.AArch64.Public.basicMm, VG.Impl.Bignum.AArch64.montMul, Code.all,
    h1, h2, h3, h4, h5, h6, h7, h8, Bool.and_true] <;>
  first
    | (obtain ⟨rfl, rfl, rfl⟩ := hx; rw [h9]; rfl)
    | rfl

def variant : RoundImpl where
  mont := Mont.base
  roundMont := Mont.calledProductEight
  noFrames := by decide +kernel
  mmNoFrames := squareEightCall_noFrames
  noDit := by lit_decide
  mmNoDit := squareEightCall_noDit
  suffix := ""
  features := []

end VG.Proof.Variants.MillerRabin.AArch64.Base
