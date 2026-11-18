module

public import VerifiedGarbage.Impl.P384.X86_64.Joint
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.X86_64.MulPX
import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Impl.P384.X86_64.Joint
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.X86_64.MulPX
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
public import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.P384.X86_64

/-! ### `P384.X86_64.FieldTmpl`, which this module and modules that import it used -/

section

/-!
# P-384 on x86-64: the templates of the field operations

The erased code of P-384's field operations modulo `p` (`FieldTmpl`,
`Proof/Weierstrass/X86_64/FieldErase.lean`), with and without BMI2 and ADX,
as literals, proven to be the code of every slot's operation by the
kernel's evaluation of the code with the slots variables.
-/

@[expose] public section

namespace VG.Proof.P384.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64

/-- The templates modulo `p`. -/
def_literal p384T := FieldTmpl.ofMod p384.MP'

/-- The templates modulo `p`, with BMI2 and ADX. -/
def_literal p384XT := FieldTmpl.ofMod p384x.MP'

section
variable {M : Impl.Mont.Mod} (hn : M.n = 6) (hs : M.sparse = true) (hk : Impl.Mont.X86_64.prodK? M = none)
include hn hs hk

theorem mul_ne {o a b : Nat} (h : a ≠ b) :
    Impl.Mont.X86_64.mul M o a b =
      Impl.Mont.X86_64.mulRounds M a b ++
        Impl.Mont.X86_64.csub M ((List.range M.n).map (Impl.Mont.X86_64.win M.n M.n))
          (Impl.Mont.X86_64.win M.n M.n M.n) ++
        Impl.Mont.X86_64.stores ((List.range M.n).map (Impl.Mont.X86_64.win M.n M.n)) o := by
  simp only [Impl.Mont.X86_64.mul, Impl.Mont.X86_64.mulR, Impl.Mont.X86_64.mulG, hn, hs, hk, h]
  rfl

theorem mul_eq (o a : Nat) : Impl.Mont.X86_64.mul M o a a = Impl.Mont.X86_64.sqrS M o a := by
  simp only [Impl.Mont.X86_64.mul, Impl.Mont.X86_64.mulR, hn, hs, hk]
  rfl

end

theorem add_eq {M : Impl.Mont.Mod} (hn : M.n = 6) (o a b : Nat) :
    Impl.Mont.X86_64.add M o a b = Impl.Mont.X86_64.addR M o a b := by
  simp only [Impl.Mont.X86_64.add, hn, show 6 < 7 from by decide, ite_true]

theorem sub_eq {M : Impl.Mont.Mod} (hn : M.n = 6) (hs : M.sparse = true)
    (hr : (M.adx = true ∧ M.red = .friendly Impl.Mont.X86_64.p256Ws) = False) (o a b : Nat) :
    Impl.Mont.X86_64.sub M o a b = Impl.Mont.X86_64.sub384 o a b := by
  unfold Impl.Mont.X86_64.sub
  rw [ite_eq_right_of_eq_false _ _ hr]
  simp only [hn, hs, and_self, ite_true]

/-- With its products written out (`Mod.inl`), `p384`'s modulus calls none. -/
theorem p384h_callOf : Mont.callOf { p384.MP' with inl := true } = none := by
  unfold Mont.callOf
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel)]

/-- The templates modulo `p`, for the products written out. -/
theorem p384HT_ok : p384T.Ok { p384.MP' with inl := true } where
  mul o a b h := by rw [mul_ne (by decide +kernel) (by decide +kernel) (by decide +kernel) h]; kernel_rfl
  sqr o a := by rw [mul_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  add o a b _ := by rw [add_eq (by decide +kernel)]; kernel_rfl
  dbl o a := by rw [add_eq (by decide +kernel)]; kernel_rfl
  sub o a b := by rw [sub_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  call f body hf o a b := by rw [p384h_callOf] at hf; cases hf

/-- With its products written out (`Mod.inl`), `p384x`'s modulus calls none. -/
theorem p384xh_callOf : Mont.callOf { p384x.MP' with inl := true } = none := by
  unfold Mont.callOf
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel)]

/-- The templates modulo `p` with BMI2 and ADX, for the products written out. -/
theorem p384XHT_ok : p384XT.Ok { p384x.MP' with inl := true } where
  mul o a b h := by rw [mul_ne (by decide +kernel) (by decide +kernel) (by decide +kernel) h]; kernel_rfl
  sqr o a := by rw [mul_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  add o a b _ := by rw [add_eq (by decide +kernel)]; kernel_rfl
  dbl o a := by rw [add_eq (by decide +kernel)]; kernel_rfl
  sub o a b := by rw [sub_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  call f body hf o a b := by rw [p384xh_callOf] at hf; cases hf

end VG.Proof.P384.X86_64

end

end

/-! Baseline and ADX taint checks of P-384's joint verifier's point additions.

The field arithmetic is checked without its displacements, as the
templates of its operations (`FieldTmpl`), each analysed once. -/

@[expose] public section

namespace VG.Proof.P384.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.P384.X86_64
open VG.Proof.Weierstrass.X86_64

/-- The window of the joint verifier, baseline and with ADX. -/
def nafJacWin := publicJoint.K
def nafJacWinAdx := publicJointAdx.K

theorem nafCachedJac_checks : CachedJacChecks nafJacWin nafJacWin.R nafJacWin.E nafJacWin.D 6160 := by
  have hT : p384T.Ok nafJacWin.M := p384HT_ok
  constructor
  iterate 6 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 3 exact hT.constantTimeB (by decide) (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem nafCachedJac_adx_checks :
    CachedJacChecks nafJacWinAdx nafJacWinAdx.R nafJacWinAdx.E nafJacWinAdx.D 6160 := by
  have hT : p384XT.Ok nafJacWinAdx.M := p384XHT_ok
  constructor
  iterate 6 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 3 exact hT.constantTimeB (by decide) (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem nafMixedJac_checks : JacMixedChecks nafJacWin nafJacWin.R nafJacWin.E nafJacWin.D := by
  have hT : p384T.Ok nafJacWin.M := p384HT_ok
  constructor
  iterate 5 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 3 exact hT.constantTimeB (by decide) (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem nafMixedJac_adx_checks : JacMixedChecks nafJacWinAdx nafJacWinAdx.R nafJacWinAdx.E nafJacWinAdx.D := by
  have hT : p384XT.Ok nafJacWinAdx.M := p384XHT_ok
  constructor
  iterate 5 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 3 exact hT.constantTimeB (by decide) (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P384.X86_64
