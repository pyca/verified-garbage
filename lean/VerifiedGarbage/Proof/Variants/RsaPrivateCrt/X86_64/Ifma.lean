module

import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Framework.X86_64.InstrBits
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64.Ifma
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
public import VerifiedGarbage.Proof.Rsa.X86_64.IfmaLit
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Precomputed
public import VerifiedGarbage.Proof.Rsa.X86_64.Calls
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Main
public import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
public import VerifiedGarbage.Proof.Bignum.CrtMath
public import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddWord
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderSave
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowS
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Accumulate
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Head
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Core
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRaw
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMont
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCross
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRow
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailSetup
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareChoice
public import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
public import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedIO
public import VerifiedGarbage.Proof.Bignum.X86_64.Copy
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPMq
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFront
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
public import VerifiedGarbage.Proof.Bignum.X86_64.Csub
public import VerifiedGarbage.Proof.Bignum.X86_64.Double
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTChecked
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedLoop
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Conv
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Core
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CoreU
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Post
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubExp
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubCT
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.StepU
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Vec
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.VecR
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
public import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
public import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
public import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
public import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
public import VerifiedGarbage.Proof.Bignum.X86_64.Row
public import VerifiedGarbage.Proof.Bignum.X86_64.Setup
public import VerifiedGarbage.Proof.Bignum.X86_64.Valid
public import VerifiedGarbage.Proof.Bignum.X86_64.WordIOLoad
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Framework.X86_64.StraightY
public import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTCode
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
public import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
public import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.Inv
public import VerifiedGarbage.Proof.Rsa.X86_64.Loops
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
public import VerifiedGarbage.Proof.Rsa.X86_64.CvCode
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquare
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxStep

/-!
# `vg_rsa_private_crt` on x86-64: with AVX512_IFMA: the variant's code and proofs

The variant `VG.Variants.RsaPrivateCrt.X86_64.Ifma.variant`
(`Variants/RsaPrivateCrt/X86_64/Ifma.lean`), with the proofs its interface
asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.X86_64.Ifma

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

open VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt VG.Impl.Bignum.X86_64 VG.Proof.Bignum.X86_64.Ifma

/-- The tests of the instructions of the two instances' code, which the
kernel evaluates in one declaration, with one match for each instruction
(`Proof/Framework/X86_64/InstrBits.lean`): their calls can be inlined, and no
instruction writes `rsp`. -/
theorem codeP_bits :
    (CrtIfma.codeP CrtIfma.lay2048 CallMont.adx.mm).InlineOkB (bSp + bNs) = true ∧
    (CrtIfma.codeP CrtIfma.lay2048z CallMont.adx.mm).InlineOkB (bSp + bNs) = true := by
  lit_decide

/-- No instruction of the code that `Mont.fnAdx`'s is inlined in loads MXCSR:
the parts of it that `Ifma.codeP_correct` and `Ifma.codeP_constantTime` ask
this of, in one declaration. -/
theorem codeP_noMx :
    (seqs (nSetupP Mont.fnAdx.mm ++ primesSetup ++ checksP)).allInstrs (fun i => !loadsMxcsr i) = true ∧
    (seqs (CrtIfma.preP Mont.fnAdx.mm)).allInstrs (fun i => !loadsMxcsr i) = true ∧
    (seqs (CrtIfma.postP Mont.fnAdx.mm)).allInstrs (fun i => !loadsMxcsr i) = true ∧
    (seqs (qPhase Mont.fnAdx.mm (CrtExpL.w4 Mont.fnAdx).code ++
      pPhase Mont.fnAdx.mm (CrtExpL.w4 Mont.fnAdx).code)).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

/-- What `l2`'s instance needs of its code with the calls inlined. -/
theorem codeP_inlined {l2 : CrtIfma.Lay} (h2 : Lay2 l2) :
    (∀ s, crtContractP.pre s → ∃ t s', Exec isa (CrtIfma.codeP l2 Mont.fnAdx.mm) s t s' ∧ abiPreserved s s' ∧
      crtContractP.post s s') ∧
    ConstantTime isa crtContractP.pre crtContractP.pub (CrtIfma.codeP l2 Mont.fnAdx.mm) :=
  ⟨Ifma.codeP_correct h2 Mont.fnAdx codeP_noMx.1 codeP_noMx.2.1 codeP_noMx.2.2.1 codeP_noMx.2.2.2,
    Ifma.codeP_constantTime Mont.fnAdx h2 codeP_noMx.2.1 codeP_noMx.2.2.1⟩

theorem inline2048 :
    (CrtIfma.codeP CrtIfma.lay2048 CallMont.adx.mm).inline = CrtIfma.codeP CrtIfma.lay2048 Mont.fnAdx.mm := by
  kernel_rfl

theorem inline2048z :
    (CrtIfma.codeP CrtIfma.lay2048z CallMont.adx.mm).inline = CrtIfma.codeP CrtIfma.lay2048z Mont.fnAdx.mm := by
  kernel_rfl

def variant : CrtImpl where
  pubOp := VG.Proof.Variants.RsaPublicPrecomputed.X86_64.Ifma.variant
  nameP := "vg_rsa_private_crt_precomputed" ++ "_ifma"
  codeP := Impl.Rsa.X86_64.CrtIfma.codeP Impl.Rsa.X86_64.CrtIfma.lay2048 CallMont.adx.mm
  depthP := by lit_decide
  okP := crtP_call_ok (Code.inlineOk_of_B codeP_bits.1) (inline2048 ▸ (codeP_inlined (.inl rfl)).1)
  ctP := crtP_call_ct (Code.inlineOk_of_B codeP_bits.1) (inline2048 ▸ (codeP_inlined (.inl rfl)).1)
    (inline2048 ▸ (codeP_inlined (.inl rfl)).2)
  nospP := noSp_of (Code.noRsp_of_bits rfl (Code.allInstrs_of_inlineOkB codeP_bits.1))
  spSafeP := Code.spSafe_of_bits rfl (Code.allInstrs_of_inlineOkB codeP_bits.1)
  suffix := "_ifma"
  features := ["avx", "avx512f", "avx512ifma", "avx512vl", "bmi2", "adx"]

/-- With `ammCoreZ` for 2048-bit keys, where the CPU also has AVX512_FP16:
of the CPUs with AVX512_IFMA, those that multiply in two 512-bit units,
where it is the faster. -/
def variant512 : CrtImpl where
  pubOp := VG.Proof.Variants.RsaPublicPrecomputed.X86_64.Ifma.variant
  nameP := "vg_rsa_private_crt_precomputed" ++ "_ifma512"
  codeP := Impl.Rsa.X86_64.CrtIfma.codeP Impl.Rsa.X86_64.CrtIfma.lay2048z CallMont.adx.mm
  depthP := by lit_decide
  okP := crtP_call_ok (Code.inlineOk_of_B codeP_bits.2) (inline2048z ▸ (codeP_inlined (.inr rfl)).1)
  ctP := crtP_call_ct (Code.inlineOk_of_B codeP_bits.2) (inline2048z ▸ (codeP_inlined (.inr rfl)).1)
    (inline2048z ▸ (codeP_inlined (.inr rfl)).2)
  nospP := noSp_of (Code.noRsp_of_bits rfl (Code.allInstrs_of_inlineOkB codeP_bits.2))
  spSafeP := Code.spSafe_of_bits rfl (Code.allInstrs_of_inlineOkB codeP_bits.2)
  suffix := "_ifma512"
  features := ["avx", "avx512f", "avx512ifma", "avx512vl", "bmi2", "adx"]
  extra := ["avx512fp16"]

end VG.Proof.Variants.RsaPrivateCrt.X86_64.Ifma
