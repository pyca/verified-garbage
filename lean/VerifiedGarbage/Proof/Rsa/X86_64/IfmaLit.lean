module

public import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
meta import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
import VerifiedGarbage.Proof.Bignum.Amm52
meta import VerifiedGarbage.Proof.Bignum.Amm52
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddWord
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCopy
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowS
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowSCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Accumulate
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Head
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Loop
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tail
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tile
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonal
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalChoice
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareFinish
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareMont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideGeneral
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRows
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareDispatch
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRawCrossCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsChoiceCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailSetup
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Block
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Math
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8RowCore
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Word
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPMq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTLoop
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCounter
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedStep
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Conv
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Core
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CoreU
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Post
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.StepU
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Vec
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.VecR
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PcFn
import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StraightY
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CallPatch
import VerifiedGarbage.Proof.Rsa.X86_64.Calls
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTCode
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT1
import VerifiedGarbage.Proof.Rsa.X86_64.RpCands
import VerifiedGarbage.Proof.Rsa.X86_64.RpExp
import VerifiedGarbage.Proof.Rsa.X86_64.RpFin
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.Rsa.X86_64.RpHalf
import VerifiedGarbage.Proof.Rsa.X86_64.RpLt
import VerifiedGarbage.Proof.Rsa.X86_64.RpMont
import VerifiedGarbage.Proof.Rsa.X86_64.RpOut
import VerifiedGarbage.Proof.Rsa.X86_64.RpProd
import VerifiedGarbage.Proof.Rsa.X86_64.RpRest
import VerifiedGarbage.Proof.Rsa.X86_64.RpSkip
import VerifiedGarbage.Proof.Rsa.X86_64.RpSq
meta import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCopy
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowS
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowSCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Accumulate
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Head
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tail
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tile
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonal
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalChoice
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareFinish
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareMont
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideGeneral
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareDispatch
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRawCrossCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsChoiceCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Block
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Math
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8RowCore
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Word
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPMq
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTLoop
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCounter
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Conv
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Core
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CoreU
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Post
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.StepU
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Vec
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.VecR
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcFn
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.StraightY
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
meta import VerifiedGarbage.Proof.Rsa.X86_64.CallPatch
meta import VerifiedGarbage.Proof.Rsa.X86_64.Calls
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTCode
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT1
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCands
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpExp
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFin
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpHalf
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpLt
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpMont
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpOut
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpProd
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpRest
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpSkip
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpSq

/-!
# RSA-CRT with AVX512_IFMA on x86-64: the code as a literal

`vg_rsa_private_crt_ifma`'s vector code is unrolled, so the kernel would build
its instructions again in every check that evaluates it (`InlineOk`, the
stack depth, `spSafe`, in the registration file and the variant): the literal
of the code (`materialize_code`, `Proof/Framework/Lit.lean`) is checked once
here instead.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

materialize_code crtIfma := Impl.Rsa.X86_64.CrtIfma.code CallMont.adx.mm

end VG.Proof.Rsa.X86_64
