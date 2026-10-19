module

import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyVerified
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyVerified
public import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseLocal
meta import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyMain
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyMain
import VerifiedGarbage.Proof.Ed448.X86_64.BaseMain
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseMain
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
import VerifiedGarbage.Proof.Ed448.X86_64.BaseEncode
import VerifiedGarbage.Proof.Ed448.X86_64.BaseField
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLoop
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Verified
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarIO
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarLoop
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarMain
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyChecks
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyDecode
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Digit
import VerifiedGarbage.Proof.Ed448.X86_64.Window.DirectKey
import VerifiedGarbage.Proof.Ed448.X86_64.Window.First
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Joint
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Register
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Round
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Coords
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Digit
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Init
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Joint
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Load
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Loop
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Math
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Write
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.X86_64.AddSub
import VerifiedGarbage.Proof.X448.X86_64.Adx.Mul
import VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X448.X86_64.Bits
import VerifiedGarbage.Proof.X448.X86_64.Freeze
import VerifiedGarbage.Proof.X448.X86_64.Main
import VerifiedGarbage.Proof.X448.X86_64.Pow223
import VerifiedGarbage.Proof.X448.X86_64.Pow223Verified
meta import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseEncode
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseField
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseLoop
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Verified
meta import VerifiedGarbage.Proof.Ed448.X86_64.ScalarIO
meta import VerifiedGarbage.Proof.Ed448.X86_64.ScalarLoop
meta import VerifiedGarbage.Proof.Ed448.X86_64.ScalarMain
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyChecks
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyDecode
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Digit
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.DirectKey
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.First
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Joint
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Register
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Round
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Coords
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Digit
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Init
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Joint
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Load
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Loop
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Math
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Write
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.X448.Bytes
meta import VerifiedGarbage.Proof.X448.X86_64.AddSub
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Mul
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr
meta import VerifiedGarbage.Proof.X448.X86_64.Bits
meta import VerifiedGarbage.Proof.X448.X86_64.Freeze
meta import VerifiedGarbage.Proof.X448.X86_64.Main
meta import VerifiedGarbage.Proof.X448.X86_64.Pow223
meta import VerifiedGarbage.Proof.X448.X86_64.Pow223Verified

/-! The same scalar and verification contracts for every field backend. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64

theorem scalarBaseFor_inlineOk (v : Impl.Ed448.X86_64.FieldVariant) :
    (scalarBaseFor v).InlineOk = true := by
  cases v
  · exact scalarBase_inlineOk
  · exact scalarBaseAdx_inlineOk

theorem scalarBaseFor_okI (v : Impl.Ed448.X86_64.FieldVariant) (hL : Proof.Ed448.BaseLadderOk)
    (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa (scalarBaseFor v).inline s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBaseFor_correct_inline v hL hs
  exact ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; cases v <;> lit_decide) he h.1, h.2⟩

theorem scalarBaseFor_ok (v : Impl.Ed448.X86_64.FieldVariant) (hL : Proof.Ed448.BaseLadderOk) :
    ∀ s, scalarBaseLocal.clear.pre s →
      ∃ t s', Exec isa (scalarBaseFor v) s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' :=
  ok_of_inline (scalarBaseFor_inlineOk v) (scalarBaseFor_okI v hL) scalarBase_patch

theorem scalarBaseFor_ct0 (v : Impl.Ed448.X86_64.FieldVariant) :
    ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub (scalarBaseFor v) := by
  cases v
  · exact scalarBase_ct0
  · change ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBaseAdx
    exact VG.Taint.constantTime (A := taint) scalarBaseτ
      (fun _ _ h₁ h₂ hp => scalarBase_agree h₁ h₂ hp) (by taint_decide)

theorem scalarBaseFor_ct (v : Impl.Ed448.X86_64.FieldVariant) :
    ConstantTime isa scalarBaseLocal.clear.pre scalarBaseLocal.pub (scalarBaseFor v) :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
    scalarBaseFor_ct0 v s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1 hp e₁ e₂

theorem scalarBaseFor_verified (v : Impl.Ed448.X86_64.FieldVariant) (hL : Proof.Ed448.BaseLadderOk) :
    Verified X86_64.target (scalarBaseFor v) (Spec.Ed448.scalarBaseContract X86_64.abi 8) :=
  Verified.of_inline_ct (scalarBaseFor_inlineOk v) (scalarBaseFor_okI v hL) (scalarBaseFor_ct0 v)
    scalarBase_implies8 (fun _ h => Sig.clear_of_pre h)
    (fun s b hv u hs hp => scalarBase_patch s b hv u (scalarBase_implies8.pre s hs) (Sig.clear_of_pre hs) hp)

theorem verifyEquationFor_inlineOk (v : Impl.Ed448.X86_64.FieldVariant) :
    (verifyEquationFor v).InlineOk = true := by
  cases v
  · exact verifyEquation_inlineOk
  · exact verifyEquationAdx_inlineOk

theorem verifyEquationFor_okI (v : Impl.Ed448.X86_64.FieldVariant)
    (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) (s : State)
    (hs : verifyEquationLocal.pre s) :
    ∃ t s', Exec isa (verifyEquationFor v).inline s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := verifyEquationFor_correct_inline v hR hE hs
  exact ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; cases v <;> lit_decide) he h.1, h.2⟩

theorem verifyEquationFor_ok (v : Impl.Ed448.X86_64.FieldVariant)
    (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) :
    ∀ s, verifyEquationLocal.clear.pre s →
      ∃ t s', Exec isa (verifyEquationFor v) s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s' :=
  ok_of_inline (verifyEquationFor_inlineOk v) (verifyEquationFor_okI v hR hE) verifyEquation_patch

theorem verifyEquationFor_ct (v : Impl.Ed448.X86_64.FieldVariant)
    (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) :
    ConstantTime isa verifyEquationLocal.clear.pre verifyEquationLocal.pub (verifyEquationFor v) :=
  ct_of_inline (verifyEquationFor_inlineOk v)
    (fun s hs => let ⟨t, u, he, _⟩ := verifyEquationFor_okI v hR hE s hs; ⟨t, u, he⟩)
    (fun _ _ h => h.1) (verifyEquationFor_ctI v hR)

theorem verifyEquationFor_verified (v : Impl.Ed448.X86_64.FieldVariant)
    (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) :
    Verified X86_64.target (verifyEquationFor v) (Spec.Ed448.verifyEquationContract X86_64.abi 8) :=
  Verified.of_inline (verifyEquationFor_inlineOk v) (verifyEquationFor_okI v hR hE)
    (verifyEquationFor_ctI v hR) verifyEquation_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ _ hp => hp)
    (fun s t hs ht hp => (verifyEquation_implies8.pub s t hs ht hp).1)

end VG.Proof.Ed448.X86_64
