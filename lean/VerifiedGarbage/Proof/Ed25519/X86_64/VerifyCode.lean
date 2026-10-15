module

import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyLit
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCall
public import VerifiedGarbage.Proof.Ed25519.X86_64.WindowSlideCT
public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.VerifyCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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

/-! `ctlOk` and `Code.InlineOk` check a block with `List.all`; the kernel evaluates the same checks
three times faster with the block's list folded by `List.rec`, as `Code.allInstrs` does. -/

/-- `is.all p`, for the kernel. -/
def allR (p : Instr → Bool) (is : List Instr) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun i _ ih => p i && ih) is

theorem allR_eq (p : Instr → Bool) : ∀ is, allR p is = is.all p
  | [] => rfl
  | i :: is => by rw [List.all_cons, ← allR_eq p is]; rfl

/-- `ctlOk`, for the kernel. -/
def ctlOkR : Prog isa → Bool
  | .block is => allR (fun i => !loadsMxcsr i) is
  | .seq a b => restores a b || (ctlOkR a && ctlOkR b)
  | .ite _ t e => ctlOkR t && ctlOkR e
  | .loop b _ => ctlOkR b
  | .call _ b => ctlOkR b
  | .frame i b j => !loadsMxcsr i && ctlOkR b && !loadsMxcsr j

theorem ctlOkR_eq : ∀ c : Prog isa, ctlOkR c = ctlOk c
  | .block is => by simp only [ctlOkR, ctlOk, allR_eq]
  | .seq a b => by simp only [ctlOkR, ctlOk, ctlOkR_eq a, ctlOkR_eq b]
  | .ite _ t e => by simp only [ctlOkR, ctlOk, ctlOkR_eq t, ctlOkR_eq e]
  | .loop b _ => by simp only [ctlOkR, ctlOk, ctlOkR_eq b]
  | .call _ b => by simp only [ctlOkR, ctlOk, ctlOkR_eq b]
  | .frame i b j => by simp only [ctlOkR, ctlOk, ctlOkR_eq b]

/-- `Code.InlineOk`, for the kernel. -/
def inlineOkR : Prog isa → Bool
  | .block l => allR (fun i => !Taint.clobbers i .rsp) l
  | .seq a b => inlineOkR a && inlineOkR b
  | .ite _ t e => inlineOkR t && inlineOkR e
  | .loop b _ => inlineOkR b
  | .call _ b => b.noCalls && b.allInstrs Instr.rspFree
  | .frame .. => false

theorem inlineOkR_eq : ∀ c : Prog isa, inlineOkR c = c.InlineOk
  | .block is => by simp only [inlineOkR, Code.InlineOk, allR_eq]
  | .seq a b => by simp only [inlineOkR, Code.InlineOk, inlineOkR_eq a, inlineOkR_eq b]
  | .ite _ t e => by simp only [inlineOkR, Code.InlineOk, inlineOkR_eq t, inlineOkR_eq e]
  | .loop b _ => by simp only [inlineOkR, Code.InlineOk, inlineOkR_eq b]
  | .call _ b => by simp only [inlineOkR, Code.InlineOk]
  | .frame .. => by simp only [inlineOkR, Code.InlineOk]

theorem baseline_mx : ctlOk (verifyEquation Impl.X25519.X86_64.baseline
    (windows Impl.X25519.X86_64.baseline)) = true := by
  rw [← ctlOkR_eq]; lit_decide

theorem baseline_spSafe : (verifyEquation Impl.X25519.X86_64.baseline
    (windows Impl.X25519.X86_64.baseline)).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

theorem adx_mx : ctlOk (verifyEquation Impl.X25519.X86_64.adx
    (windows Impl.X25519.X86_64.adx)) = true := by
  rw [← ctlOkR_eq]; lit_decide

theorem adx_spSafe : (verifyEquation Impl.X25519.X86_64.adx
    (windows Impl.X25519.X86_64.adx)).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

theorem ifma_mx : ctlOk (verifyEquation Impl.X25519.X86_64.adx
    Ifma.windows) = true := by
  rw [← ctlOkR_eq]; lit_decide

theorem ifma_spSafe : (verifyEquation Impl.X25519.X86_64.adx
    Ifma.windows).all
    (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

theorem baseline_inlineOk : (verifyEquation Impl.X25519.X86_64.baseline
    (windows Impl.X25519.X86_64.baseline)).InlineOk = true := by
  rw [← inlineOkR_eq]; lit_decide

theorem adx_inlineOk : (verifyEquation Impl.X25519.X86_64.adx
    (windows Impl.X25519.X86_64.adx)).InlineOk = true := by
  rw [← inlineOkR_eq]; lit_decide

theorem ifma_inlineOk : (verifyEquation Impl.X25519.X86_64.adx Ifma.windows).InlineOk = true := by
  rw [← inlineOkR_eq]; lit_decide

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
