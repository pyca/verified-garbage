module

public import VerifiedGarbage.Impl.P224.X86_64.Joint
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.X86_64.MulPX
import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Impl.P224.X86_64.Joint
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.X86_64.MulPX
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase

/-! ### `P224.X86_64.FieldTmpl`, which this module and modules that import it used -/

section

/-!
# P-224 on x86-64: the templates of the field operations

The erased code of P-224's field operations modulo `p` in the joint
verifier's window (`FieldTmpl`, `Proof/Weierstrass/X86_64/FieldErase.lean`),
as a literal, proven to be the code of every slot's operation by the
kernel's evaluation of the code with the slots variables.
-/

@[expose] public section

namespace VG.Proof.P224.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P224.X86_64
open VG.Proof.Weierstrass.X86_64

/-- The templates modulo `p`. -/
def_literal p224T := FieldTmpl.ofMod p224v.MH

theorem p224_callOf : Mont.callOf p224v.MH = none := by
  unfold Mont.callOf
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel)]

theorem p224T_ok : p224T.Ok p224v.MH where
  mul _ _ _ _ := by kernel_rfl
  sqr _ _ := by kernel_rfl
  add _ _ _ _ := by kernel_rfl
  dbl _ _ := by kernel_rfl
  sub _ _ _ := by kernel_rfl
  call f body hf _ _ _ := by rw [p224_callOf] at hf; cases hf

/-- The erased double of `ForwardField.programB` (`double4`). -/
def_literal p224D := KList.map Instr.erase (Impl.Mont.X86_64.double4 p224v.MH 0 8)

theorem p224D_ok (o a : Nat) : KList.map Instr.erase (Impl.Mont.X86_64.double4 p224v.MH o a) = p224D := by
  kernel_rfl

end VG.Proof.P224.X86_64

end

end

/-! Taint checks of P-224's joint verifier's point additions. -/

@[expose] public section

namespace VG.Proof.P224.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.P224.X86_64
open VG.Proof.Weierstrass.X86_64

/-- The window of the joint verifier. -/
def nafJacWin := publicJoint.K

theorem nafCachedJac_checks : CachedJacChecks nafJacWin nafJacWin.R nafJacWin.E nafJacWin.D 5408 := by
  have hT : p224T.Ok nafJacWin.M := p224T_ok
  constructor
  iterate 6 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 3 exact hT.constantTimeB4 rfl rfl p224D_ok (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem nafMixedJac_checks : JacMixedChecks nafJacWin nafJacWin.R nafJacWin.E nafJacWin.D := by
  have hT : p224T.Ok nafJacWin.M := p224T_ok
  constructor
  iterate 5 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 3 exact hT.constantTimeB4 rfl rfl p224D_ok (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P224.X86_64
