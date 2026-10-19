module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinish
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCoreCT
public meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
public meta import VerifiedGarbage.Impl.Bignum.CrtLayout
public meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinishSquare
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
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
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPending
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingMath
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawCore
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawSquares
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSquares
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailBit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
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
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
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
meta import VerifiedGarbage.TCB.AArch64.Target

/-! The final partial window branches and loops only on its public bit count. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (finishSquare finish)

def FinishPre (p : XPub × Nat) (s : State) : Prop :=
  WindowPre p.1 s ∧ p.2 < 5 ∧
  word s.mem (off p.1.B p.1.o) (8 * Crt.sBit) = BitVec.ofNat 64 p.2

theorem finishSquare_ct (M : Mont) :
    RelCT isa (Two FinishPre) (finishSquare M.mm) (fun _ _ => True) := by
  unfold finishSquare
  refine RelCT.seq (two_post (Ψ := fun p : XPub × Nat => GoodW p.1.ws)
    (two_map (fun p : XPub × Nat => p.1.ws)
      (fun _ _ ⟨⟨mi,_,_,_,hc,_⟩,_⟩ => ⟨mi,hc.good,Nat.le_refl _⟩)
      (M.ct (by simp [MmUse]))) ?_) ?_
  · rintro p s ⟨⟨mi,X,Xc,v,hc,ht,hy,hw,hw',hR,hv,hn⟩,_⟩
    exact WP.mono (crtSq_ok M (Q := False) (x := 0) (E := 0)
      hc.base hw hw' hR hy False.elim) fun t ⟨ct,_⟩ => ⟨mi,ct.good,Nat.le_refl _⟩
  · apply x0_ct (fun p : XPub × Nat => off p.1.B p.1.o) ?_ (by taint_decide)
    exact fun _ _ ⟨_,hc,_⟩ => hc.x0

theorem finishSquare_post (M : Mont) {p : XPub × Nat} {s : State}
    (h : FinishPre p s) (hb : 0 < p.2) :
    WP isa (finishSquare M.mm) s fun t =>
      FinishPre (p.1,p.2 - 1) t ∧ t.gpr .x3 = BitVec.ofNat 64 (p.2 - 1) := by
  obtain ⟨⟨mi,X,Xc,v,hc,ht,hy,hw,hw',hR,hv,hn⟩,hb',bc⟩ := h
  refine WP.mono (finishSquare_ok M hc ht hw hw' hR hy (Q := False) (x := 0) (E := 0)
    False.elim hb bc) fun t ⟨ct,tt,yt,_,bt,h3,_,_,hh⟩ => ?_
  exact ⟨⟨⟨mi,X,Xc,v,ct,tt,yt,hw,hw',hR,hv,
    (hh _ (by decide) (by decide)).trans hn⟩,by omega,bt⟩,h3⟩

theorem finishSquares_ct (M : Mont) :
    RelCT isa (Two fun p s => 0 < p.2 ∧ FinishPre p s)
      (.loop (finishSquare M.mm) (.nonzero .x .x3))
      (Two fun (p : XPub × Nat) s => FinishPre (p.1,0) s) := by
  refine two_loop (Φ := fun (p : XPub × Nat) i => FinishPre (p.1,p.2-i)) Prod.snd ?_ ?_
  · exact two_map (fun p : (XPub × Nat) × Nat => (p.1.1,p.1.2-p.2))
      (fun _ _ h => h.2) (finishSquare_ct M)
  · intro p i s hi hs
    refine WP.mono (finishSquare_post M hs (by omega)) fun t ⟨ht,h3⟩ => ?_
    refine ⟨?_,?_,?_⟩
    · exact eval_nz_count hi (by rw [h3,cnt_ne (by have := hs.2.1; omega)]; omega)
    · intro _; simpa only [Nat.sub_sub] using ht
    · intro he; simpa only [Nat.sub_sub,he,Nat.sub_self] using ht

theorem selectProduct_ct (M : Mont) (S : Selector) :
    RelCT isa (Two WindowPre) (.seq S.code (M.mm aY aY Crt.aT)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p : XPub => GoodW p.ws)
    (two_map id (fun _ _ h => h.sel) S.ct) ?_)
    (two_map (fun p : XPub => p.ws) (fun _ _ h => h)
      (M.ct (o := aY) (a := aY) (b := Crt.aT) (by unfold MmUse; decide)))
  rintro p s ⟨mi,X,Xc,v,hc,ht,_,hw,hw',_,hv,hn⟩
  exact WP.mono (S.ok hc hw hw' hv ht.tab hn) fun t ⟨ct,_⟩ =>
    ⟨mi,ct.good,Nat.le_refl _⟩

def FinishReady (p : XPub × Nat) (s : State) : Prop :=
  FinishPre p s ∧ s.gpr .x3 = BitVec.ofNat 64 p.2

theorem finishLoad_post {p : XPub × Nat} {s : State} (h : FinishPre p s) :
    WP isa (.block [ldh .x3 Crt.sBit]) s (FinishReady p) := by
  obtain ⟨⟨mi,X,Xc,v,hc,ht,hy,hw,hw',hR,hv,hn⟩,hb,bc⟩ := h
  refine WP.mono (finishLoad_ok hc bc) fun t ⟨⟨hm,h3⟩,kt⟩ => ?_
  have hf : Frm (off p.1.B p.1.o) (crtWinRanges p.1.wx) s.mem t.mem := hm.symm ▸ Frm.refl _ _ _
  exact ⟨⟨⟨mi,X,Xc,v,hc.of_win hf kt.wr (kt.gpr .x0 (by decide)),ht.of_win hf hc.scrT.nowrap,
    hm.symm ▸ hy,hw,hw',hR,hv,hm.symm ▸ hn⟩,hb,hm.symm ▸ bc⟩,h3⟩

theorem finish_ct (M : Mont) (S : Selector) :
    RelCT isa (Two FinishPre) (finish M.mm S.code) (fun _ _ => True) := by
  unfold finish
  refine RelCT.seq (two_post (Ψ := FinishReady)
    (x0_ct (fun p : XPub × Nat => off p.1.B p.1.o)
      (fun _ _ ⟨⟨_,_,_,_,hc,_⟩,_⟩ => hc.good.x0) (by taint_decide))
    (fun _ _ h => finishLoad_post h)) ?_
  refine two_ite ?_ ?_ ?_
  · intro p s t hs ht
    change some (!(s.gpr .x3 == 0)) = some (!(t.gpr .x3 == 0))
    rw [hs.2,ht.2]
  · refine RelCT.seq (two_map id ?_ (finishSquares_ct M))
      (two_map (fun p : XPub × Nat => p.1) (fun _ _ h => h.1) (selectProduct_ct M S))
    intro p s ⟨hs,he⟩
    refine ⟨?_,hs.1⟩
    change 0 < p.2
    by_contra hz
    have hb : p.2 = 0 := by omega
    change some (!(s.gpr .x3 == 0)) = some true at he
    rw [hs.2,hb] at he
    contradiction
  · apply two_taint [] (hc := .block [])
    · intro _ _ _ _ _ r hr; simp at hr
    · rfl

end VG.Proof.Bignum.AArch64.WindowFive
