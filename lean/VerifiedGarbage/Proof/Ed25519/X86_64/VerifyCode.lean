module

import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyLit
public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCall
public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.VerifyLit
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowSlideCT
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.VerifyCT
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Decode
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.X86_64.BaseOdd
import VerifiedGarbage.Proof.Ed25519.X86_64.Bits
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
import VerifiedGarbage.Proof.Ed25519.X86_64.CombNeg
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodePowers
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldLazy
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombSelect
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Keeps
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEncode
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEqual
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowDigits
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.X25519.X86_64.AddSub
import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.X25519.X86_64.Bits
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Main
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Step
import VerifiedGarbage.Proof.X25519.X86_64.Finish
import VerifiedGarbage.Proof.X25519.X86_64.Freeze
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Part2
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Step
import VerifiedGarbage.Proof.X25519.X86_64.Inv
import VerifiedGarbage.Proof.X25519.X86_64.Invert
import VerifiedGarbage.Proof.X25519.X86_64.Sqr

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
