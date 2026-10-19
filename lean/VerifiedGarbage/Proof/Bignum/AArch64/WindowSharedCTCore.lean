module

public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCTLoop
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedWork
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCTLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedWork
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedLoop
import VerifiedGarbage.Proof.Bignum.AArch64.WindowArithmeticCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
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
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSquares
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBlock
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
import VerifiedGarbage.Proof.Bignum.AArch64.WindowOperations
import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCT
import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCtContext
import VerifiedGarbage.Proof.Bignum.AArch64.WindowReduce
import VerifiedGarbage.Proof.Bignum.AArch64.WindowReduceCanonical
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSetup
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCore
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
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
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

def FastPre (p : XPub) (s : State) : Prop :=
  ∃ mi X Xc v, TableCtx s (off p.B p.o) p.wx mi X Xc ∧
    CrtWindowFive.CTab s.mem (off p.B p.o) p.wx X False 0 ∧
    16 ≤ p.wx ∧ p.wx < 2^30 ∧ p.wx % 8 = 0 ∧ v < 32 ∧
    word s.mem (off p.B p.o) (8*Crt.sNib) = BitVec.ofNat 64 v

def CorePre (p : XPub) (s : State) : Prop :=
  FastPre p s ∧ word s.mem (off p.B p.o) (8*Crt.sBit) = BitVec.ofNat 64 5

theorem fast_loose {p : XPub} {s : State} (h : FastPre p s) : LooseCtx p s := by
  obtain ⟨mi,X,Xc,v,hc,ht,hw,hw',hd,hv,hn⟩ := h
  exact ⟨mi,X,Xc,hc,hw,hw',hd⟩

theorem squares_post (p : XPub) (s : State) (h : CorePre p s) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.squares s (FastPre p) := by
  obtain ⟨⟨mi,X,Xc,v,hc,ht,hw,hw',hd,hv,hn⟩,hb⟩ := h
  refine WP.mono (squares_ok hc hw hw' hd hb) fun t ⟨ct,_,hh,hf,_⟩ => ?_
  exact ⟨mi,X,Xc,v,ct,ht.of_win hf hc.scrT.nowrap,hw,hw',hd,hv,
    (hh _ (by decide) (by decide)).trans hn⟩

theorem core_ct : RelCT isa (Two CorePre)
    VG.Impl.Rsa.AArch64.WindowShared.core (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowShared.core
  refine RelCT.seq (two_post (two_map id (fun _ _ h => ⟨fast_loose h.1,h.2⟩)
    (loop_ct.mono (fun _ _ h => h) (fun _ _ _ => True.intro))) squares_post) ?_
  refine RelCT.seq (two_post (Ψ := fun p => BlockedRedc.FastW (workspace p))
    (two_map id ?_ WindowVector.blocked_ct) ?_)
    (two_map workspace (fun _ _ h => h) WindowArithmetic.product_ct)
  · rintro p s ⟨mi,X,Xc,v,hc,ht,hw,hw',hd,hv,hn⟩
    exact ⟨⟨mi,X,Xc,v,hc,by change 2 ≤ p.wx; omega,hw',hv,ht.tab,hn⟩,by change 8 ≤ p.wx; omega⟩
  · rintro p s ⟨mi,X,Xc,v,hc,ht,hw,hw',hd,hv,hn⟩
    exact WP.mono (WindowVector.blocked_ok hc (by omega) hw' hd hv ht.tab hn)
      fun t ⟨ct,_⟩ => ⟨⟨mi,ct.good,Nat.le_refl _⟩,hw,hd⟩

theorem init_post (p : XPub) (s : State) (h : FastPre p s) :
    WP isa (.block [movi .x3 5,sth .x3 Crt.sBit]) s (CorePre p) := by
  obtain ⟨mi,X,Xc,v,hc,ht,hw,hw',hd,hv,hn⟩ := h
  refine WP.mono (init_ok hc) fun t ⟨hm,kt⟩ => ?_
  have hout := writeW_outside s.mem (off p.B p.o) (d := 8*Crt.sBit) (BitVec.ofNat 64 5) (by decide)
  rw [← hm] at hout
  have hf : Frm (off p.B p.o) (crtWinRanges p.wx) s.mem t.mem :=
    Frm.of_outside hout (by simp [crtWinRanges])
  refine ⟨⟨mi,X,Xc,v,hc.of_win hf kt.wr (kt.gpr .x0 (by decide)),
    ht.of_win hf hc.scrT.nowrap,hw,hw',hd,hv,?_⟩,?_⟩
  · rw [hm,hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hn
  · rw [hm,word_writeW_self]

theorem work_ct : RelCT isa (Two FastPre)
    VG.Impl.Rsa.AArch64.WindowShared.work (fun _ _ => True) :=
  RelCT.seq (two_piece [.x0] (fun p s t hs ht => pins_loose p s t (fast_loose hs) (fast_loose ht))
    (by taint_decide) init_post) core_ct

end VG.Proof.Bignum.AArch64.WindowShared
