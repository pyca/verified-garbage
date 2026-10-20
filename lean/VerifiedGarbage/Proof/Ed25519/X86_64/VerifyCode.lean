module

import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyLit
public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCall
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowSlideCT
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.VerifyCT
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyIfma
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.VerifyLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# Facts about the code of each registered verification

That every load of MXCSR restores it (`ctlOk`, the hypothesis of
`verify_verified`) and that no instruction writes the stack pointer, for each
field multiplication and doubling `vg_ed25519_verify_equation` is registered
with: evaluated once here, from the literals, for both the equation's own
artifacts and the generic verification over SHA-512 that calls it.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.VerifyCode

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

theorem baseline_mx : ctlOk (verifyEquation Impl.X25519.X86_64.baseline
    (windows Impl.X25519.X86_64.baseline)) = true := by
  lit_decide

theorem baseline_spSafe : (verifyEquation Impl.X25519.X86_64.baseline
    (windows Impl.X25519.X86_64.baseline)).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

theorem adx_mx : ctlOk (verifyEquation Impl.X25519.X86_64.adx
    (windows Impl.X25519.X86_64.adx)) = true := by
  lit_decide

theorem adx_spSafe : (verifyEquation Impl.X25519.X86_64.adx
    (windows Impl.X25519.X86_64.adx)).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

theorem ifma_mx : ctlOk (verifyEquation Impl.X25519.X86_64.adx
    Ifma.windows) = true := by
  lit_decide

theorem ifma_spSafe : (verifyEquation Impl.X25519.X86_64.adx
    Ifma.windows).all
    (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

theorem baseline_inlineOk : (verifyEquation Impl.X25519.X86_64.baseline
    (windows Impl.X25519.X86_64.baseline)).InlineOk = true := by
  lit_decide

theorem adx_inlineOk : (verifyEquation Impl.X25519.X86_64.adx
    (windows Impl.X25519.X86_64.adx)).InlineOk = true := by
  lit_decide

theorem ifma_inlineOk : (verifyEquation Impl.X25519.X86_64.adx Ifma.windows).InlineOk = true := by
  lit_decide

/-- No instruction of code that inlines writes `rsp`, from `Code.InlineOk` rather than a
second walk of the code. -/
theorem noSp_of_inlineOk {c : Prog isa} (h : c.InlineOk = true) :
    c.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_inline, Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  rw [Code.clobbers_rsp_of_inlineOk h i hi, Bool.not_false]

theorem baseline_noSp : (verifyEquation Impl.X25519.X86_64.baseline
    (windows Impl.X25519.X86_64.baseline)).allInstrs (fun i => !Taint.clobbers i .rsp) = true :=
  noSp_of_inlineOk baseline_inlineOk

theorem adx_noSp : (verifyEquation Impl.X25519.X86_64.adx
    (windows Impl.X25519.X86_64.adx)).allInstrs (fun i => !Taint.clobbers i .rsp) = true :=
  noSp_of_inlineOk adx_inlineOk

theorem ifma_noSp : (verifyEquation Impl.X25519.X86_64.adx Ifma.windows).allInstrs
    (fun i => !Taint.clobbers i .rsp) = true :=
  noSp_of_inlineOk ifma_inlineOk

theorem ifma_windows_inline : Ifma.windows.inline = Ifma.windows :=
  Code.inline_of_noCalls (by lit_decide)

/-- MXCSR is restored in each checker's code, its calls inlined. -/
theorem baseline_mxI : MxcsrOk (verifyEquationWith Impl.X25519.X86_64.baseline
    (Point64.bodies Impl.X25519.X86_64.baseline) (windowsWith Impl.X25519.X86_64.baseline (Point64.bodies Impl.X25519.X86_64.baseline))) := by
  rw [← verifyEquation_inline (fld := Impl.X25519.X86_64.baseline) (win' := windows Impl.X25519.X86_64.baseline)
    (win := windowsWith Impl.X25519.X86_64.baseline (Point64.bodies Impl.X25519.X86_64.baseline)) rfl]
  exact ctlOk_inline baseline_mx

theorem adx_mxI : MxcsrOk (verifyEquationWith Impl.X25519.X86_64.adx
    (Point64.bodies Impl.X25519.X86_64.adx) (windowsWith Impl.X25519.X86_64.adx (Point64.bodies Impl.X25519.X86_64.adx))) := by
  rw [← verifyEquation_inline (fld := Impl.X25519.X86_64.adx) (win' := windows Impl.X25519.X86_64.adx)
    (win := windowsWith Impl.X25519.X86_64.adx (Point64.bodies Impl.X25519.X86_64.adx)) rfl]
  exact ctlOk_inline adx_mx

theorem ifma_mxI : MxcsrOk (verifyEquationWith Impl.X25519.X86_64.adx
    (Point64.bodies Impl.X25519.X86_64.adx) Ifma.windows) := by
  rw [← verifyEquation_inline (fld := Impl.X25519.X86_64.adx) ifma_windows_inline]
  exact ctlOk_inline ifma_mx

/-- What a caller needs of each registered checker's code (`CallCode`). -/
theorem baseline_call : CallCode Impl.X25519.X86_64.baseline (windows Impl.X25519.X86_64.baseline) :=
  ⟨⟨windowsWith Impl.X25519.X86_64.baseline (Point64.bodies Impl.X25519.X86_64.baseline), inferInstance, rfl, baseline_inlineOk,
    baseline_mxI⟩⟩

theorem adx_call : CallCode Impl.X25519.X86_64.adx (windows Impl.X25519.X86_64.adx) :=
  ⟨⟨windowsWith Impl.X25519.X86_64.adx (Point64.bodies Impl.X25519.X86_64.adx), inferInstance, rfl, adx_inlineOk, adx_mxI⟩⟩

theorem ifma_call : CallCode Impl.X25519.X86_64.adx Ifma.windows :=
  ⟨⟨_, inferInstance, ifma_windows_inline, ifma_inlineOk, ifma_mxI⟩⟩

end VG.Proof.Ed25519.X86_64.VerifyCode
