module

public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCTCore
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedSave
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCTCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedSave
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedWork
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedWork
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowReset
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSquares
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBlock
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorClear
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCopy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorGuard
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorInner
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorRow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStart
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChain
import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainCore
import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainStep
import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainTile
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCount
import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonal
import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonalCore
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightBound
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightDiagonal
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightHead
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightLoad
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRaw
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRow
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.AArch64.WideDiagonal
import VerifiedGarbage.Proof.Bignum.AArch64.WindowArithmeticCT
import VerifiedGarbage.Proof.Bignum.AArch64.WindowOperations
import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCT
import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCtContext
import VerifiedGarbage.Proof.Bignum.AArch64.WindowReduce
import VerifiedGarbage.Proof.Bignum.AArch64.WindowReduceCanonical
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSetup
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCore
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedLoop
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedStep
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseCTRows
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseHead
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseHoles
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseRows
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseTail
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseTile
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowReset
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSquares
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBlock
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorClear
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCopy
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorInner
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStart
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChain
meta import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainStep
meta import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainTile
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Setup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCount
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonal
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonalCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightBound
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightDiagonal
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightHead
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Bignum.AArch64.WideDiagonal
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowArithmeticCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowOperations
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCtContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowReduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowReduceCanonical
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedStep
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseCTRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseHead
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseHoles
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseTail
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseTile
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem save_post (p : XPub) (s : State) (h : FastPre p s) :
    WP isa (.block VG.Impl.Rsa.AArch64.WindowShared.save) s (FastPre p) := by
  obtain ⟨mi,X,Xc,v,hc,ht,hw,hw',hd,hv,hn⟩ := h
  refine WP.mono (save_ok s) fun t ⟨⟨hm,_⟩,kt⟩ => ?_
  have hf : Frm (off p.B p.o) (crtWinRanges p.wx) s.mem t.mem := by rw [hm]; exact Frm.refl _ _ _
  exact ⟨mi,X,Xc,v,hc.of_win hf kt.wr (kt.gpr .x0 (by decide)),hm ▸ ht,hw,hw',hd,hv,hm ▸ hn⟩

theorem work_post (p : XPub) (s : State) (h : FastPre p s) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.work s fun t => t.gpr .x0 = off p.B p.o := by
  obtain ⟨mi,X,Xc,v,hc,ht,hw,hw',hd,hv,hn⟩ := h
  exact WP.mono (work_ok hc ht hw hw' hd hv hn) fun _ ⟨ct,_⟩ => ct.good.x0

theorem fast_ct : RelCT isa (Two FastPre)
    VG.Impl.Rsa.AArch64.WindowShared.fast (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowShared.fast
  refine RelCT.seq (two_piece [] (fun _ _ _ _ _ _ h => by simp at h)
    (by taint_decide) save_post) ?_
  refine RelCT.seq (two_post work_ct work_post) ?_
  refine RelCT.seq (two_post (two_taint [] (fun _ _ _ _ _ _ h => by simp at h) (by taint_decide))
    (fun p s h => WP.mono (restore_ok s) (fun _ ⟨_,kt⟩ => (kt.gpr .x0 (by decide)).trans h))) ?_
  exact two_taint [.x0] (pins_x0B (fun p : XPub => off p.B p.o) (fun _ _ h => h)) (by taint_decide)

end VG.Proof.Bignum.AArch64.WindowShared
