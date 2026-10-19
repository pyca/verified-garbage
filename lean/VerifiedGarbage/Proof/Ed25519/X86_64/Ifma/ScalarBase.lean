module

import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Mul
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Mul
public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedCT
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
meta import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
import VerifiedGarbage.Spec.Weierstrass
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
meta import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.BaseOdd
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Ed25519.Recode
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
import VerifiedGarbage.Proof.Ed25519.X86_64.CombNeg
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldLazy
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Keeps
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Ops
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEncode
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Consts
import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Halves
import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Keep
import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Tail
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.ZVecKeep
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
import VerifiedGarbage.Spec.EcKey.Generic
import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Impl.Ed25519.X86_64.BaseOdd
meta import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
meta import VerifiedGarbage.Proof.Ed25519.Bytes
meta import VerifiedGarbage.Proof.Ed25519.Group.Decode
meta import VerifiedGarbage.Proof.Ed25519.Recode
meta import VerifiedGarbage.Proof.Ed25519.Scalar
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CombNeg
meta import VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits
meta import VerifiedGarbage.Proof.Ed25519.X86_64.FieldLazy
meta import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLoop
meta import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMemory
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Keeps
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Ops
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointEncode
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTBatch
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Points
meta import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedCT
meta import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
meta import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Consts
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Halves
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Keep
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Tail
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx512
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.X86_64.ZVecKeep
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.X25519.X86_64.AddSub
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
meta import VerifiedGarbage.Proof.X25519.X86_64.Bits
meta import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
meta import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Main
meta import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Step
meta import VerifiedGarbage.Proof.X25519.X86_64.Finish
meta import VerifiedGarbage.Proof.X25519.X86_64.Freeze
meta import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Part2
meta import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Step
meta import VerifiedGarbage.Proof.X25519.X86_64.Inv
meta import VerifiedGarbage.Proof.X25519.X86_64.Invert
meta import VerifiedGarbage.Proof.X25519.X86_64.Sqr
meta import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.Spec.Ecdsa.Generic

/-!
# Ed25519's fixed-base multiplication with AVX512_IFMA: `Verified`

`scalarBase_ifma` is `scalarBase_precomputed adx` with the comb
`Zmm.combMultiply` (`zcomb_ok`; constant time by taint tracking, the
static's address public): correctness from the engine's (`scalarBaseEngineOf_ok`),
MXCSR's control bits kept, as the comb loads MXCSR only between saving it in
`r11` and loading it back (`ctlOk`), and the shared contract.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519.X86_64

/-- The comb with AVX512_IFMA. -/
theorem combOk : CombOk (Impl.Ed25519.X86_64.Zmm.combMultiply Impl.X25519.X86_64.adx) :=
  ⟨fun hs hS _ hb ht hfar => Zmm.zcomb_ok hs hS hb ht hfar,
    fun _ hp => taintSymFld (Taint.ofRegs [.rdi]) hp (by exact ⟨_, by taint_decide⟩)⟩

theorem comb_inline : (Impl.Ed25519.X86_64.Zmm.combMultiply Impl.X25519.X86_64.adx).inline =
    Impl.Ed25519.X86_64.Zmm.combMultiply Impl.X25519.X86_64.adx := Code.inline_of_noCalls (by lit_decide)

theorem scalarBase_ifma_okI [X25519.X86_64.DivstepInv] (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase_ifma.inline s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct_of_engine _
    (fun hs hp hr hd ht hfar => scalarBaseEngineOf_ok (fld := Impl.X25519.X86_64.adx) combOk comb_inline
      hs hp hr hd ht hfar) hs
  rw [← scalarBaseWith_inline] at he
  exact ⟨t, s', he, abiPreserved_of_ctl (by lit_decide) he h.1, h.2⟩

theorem scalarBase_ifma_ctI [X25519.X86_64.DivstepInv] :
    ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase_ifma.inline := by
  rw [scalarBase_ifma, scalarBaseWith_inline]
  exact scalarBase_ct_of_engine _ (fun hs hp hr hd ht hfar =>
      scalarBaseEngineOf_ok (fld := Impl.X25519.X86_64.adx) combOk comb_inline hs hp hr hd ht hfar)
    (scalarBaseEngineOf_ct (fld := Impl.X25519.X86_64.adx) combOk comb_inline)

theorem scalarBase_ifma_ok [X25519.X86_64.DivstepInv] :
    ∀ s, scalarBaseLocal.clear.pre s → ∃ t s', Exec isa scalarBase_ifma s t s' ∧ abiPreserved s s' ∧
      scalarBaseLocal.post s s' :=
  ok_of_inline (by lit_decide) scalarBase_ifma_okI scalarBase_patch

theorem scalarBase_ifma_ct [X25519.X86_64.DivstepInv] :
    ConstantTime isa scalarBaseLocal.clear.pre scalarBaseLocal.pub scalarBase_ifma :=
  ct_of_inline (by lit_decide) (fun s h => let ⟨t, s', e, _⟩ := scalarBase_ifma_okI s h; ⟨t, s', e⟩)
    (fun _ _ h => h.1) scalarBase_ifma_ctI

theorem scalarBase_ifma_verified [X25519.X86_64.DivstepInv] : Verified X86_64.target scalarBase_ifma
    (Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts combConsts) 8) :=
  scalarBase_verified_of (by lit_decide) scalarBase_ifma_okI scalarBase_ifma_ctI

end VG.Proof.Ed25519.X86_64.Ifma
