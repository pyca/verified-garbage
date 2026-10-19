module

import VerifiedGarbage.Proof.Bignum.AArch64.WindowArithmeticCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowArithmeticCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowShared
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtContext
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedStep
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
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCoreCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSquares
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
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedLoop
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtUnit
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowOperations
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCtContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowReduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowReduceCanonical
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSetup
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
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

def LooseCtx (p : XPub) (s : State) : Prop :=
  ∃ mi X Xc, TableCtx s (off p.B p.o) p.wx mi X Xc ∧ 16 ≤ p.wx ∧ p.wx < 2^30 ∧ p.wx % 8 = 0

def workspace (p : XPub) : Ws := ⟨off p.B p.o,slot p.wx 8,p.wx⟩

theorem loose_fast {p : XPub} {s : State} (h : LooseCtx p s) : BlockedRedc.FastW (workspace p) s := by
  obtain ⟨mi,X,Xc,hc,hw,hw',hd⟩ := h
  exact ⟨⟨mi,hc.good,Nat.le_refl _⟩,hw,hd⟩

theorem pins_loose : Pins LooseCtx [.x0] := by
  intro p s t hs ht r hr
  obtain ⟨_,_,_,cs,_⟩ := hs
  obtain ⟨_,_,_,ct,_⟩ := ht
  have : r = .x0 := by simpa using hr
  subst r
  exact cs.good.x0.trans ct.good.x0.symm

def LoopP (p : XPub) (j : Nat) (s : State) : Prop :=
  LooseCtx p s ∧ word s.mem (off p.B p.o) (8*Crt.sBit) = BitVec.ofNat 64 (5-j)

theorem square_loop_ctx (p : XPub × Nat) (s : State) (h : LoopP p.1 p.2 s) :
    WP isa (VG.Impl.Bignum.AArch64.WindowArithmetic.square 6) s (LoopP p.1 p.2) := by
  obtain ⟨⟨mi,X,Xc,hc,hw,hw',hd⟩,hb⟩ := h
  refine WP.mono (square_ok hc hw hw' hd) fun t ⟨ct,_,hh,_,_⟩ => ?_
  exact ⟨⟨mi,X,Xc,ct,hw,hw',hd⟩,(hh _ (by decide)).trans hb⟩

theorem step_ct : RelCT isa (Two fun p : XPub × Nat => fun s => p.2 < 5 ∧ LoopP p.1 p.2 s)
    VG.Impl.Rsa.AArch64.WindowShared.step (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowShared.step
  refine RelCT.seq (two_post (two_map (fun p : XPub × Nat => workspace p.1)
    (fun _ _ h => loose_fast h.2.1) WindowArithmetic.square_ct)
    (fun p s h => square_loop_ctx p s h.2)) ?_
  exact two_taint [.x0] (fun p s t hs ht => pins_loose p.1 s t hs.1 ht.1) (by taint_decide)

theorem step_loop_ctx (p : XPub) (j : Nat) (s : State) (hj : j < 5) (h : LoopP p j s) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.step s fun t =>
      LoopP p (j+1) t ∧ t.gpr .x3 = BitVec.ofNat 64 (5-(j+1)) := by
  obtain ⟨⟨mi,X,Xc,hc,hw,hw',hd⟩,hb⟩ := h
  refine WP.mono (step_ok (k := 0) (A := wv s.mem (off p.B p.o) (slot p.wx Public.aY) p.wx)
    hc hw hw' hd hj hb (by simp)) fun t ⟨ct,_,hb',h3,_⟩ => ?_
  exact ⟨⟨⟨mi,X,Xc,ct,hw,hw',hd⟩,hb'⟩,h3⟩

theorem loop_ct : RelCT isa (Two fun p s => LoopP p 0 s)
    VG.Impl.Rsa.AArch64.WindowShared.squares (Two fun p s => LoopP p 5 s) := by
  apply RelCT.mono (two_loop (fun _ : XPub => 5) step_ct ?_) (fun _ _ h => ?_) (fun _ _ h => h)
  · intro p j s hj h
    refine WP.mono (step_loop_ctx p j s hj h) fun t ⟨ht,h3⟩ => ?_
    refine ⟨?_,fun _ => ht,fun he => he ▸ ht⟩
    rw [VG.Proof.MlKem.AArch64.eval_nonzero,h3,VG.Proof.MlKem.AArch64.ne_zero_iff,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 5-(j+1) < 2^64 by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · obtain ⟨p,hs,ht,hsp⟩ := h
    exact ⟨p,⟨by decide,hs⟩,⟨by decide,ht⟩,hsp⟩

end VG.Proof.Bignum.AArch64.WindowShared
