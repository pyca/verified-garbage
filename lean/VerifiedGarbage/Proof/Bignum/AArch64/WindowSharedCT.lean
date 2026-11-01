module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawCT
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowHelperContract
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCTCore

import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCTFast
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcGuard
import VerifiedGarbage.Proof.Bignum.AArch64.WindowHelperContext
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawBody
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowHelperContract
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCTCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCTFast
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowHelperContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawBody
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff eval_zero eq_zero_iff)
open VG.Proof.Bignum.AArch64.WindowFive (RawWindowPre)

structure GuardPre (p : XPub) (s : State) : Prop where
  raw : RawWindowPre p s
  width : s.gpr .x3 = BitVec.ofNat 64 (p.wx/16)
  rem : s.gpr .x4 = BitVec.ofNat 64 (p.wx%8)

theorem guard_post (p : XPub) (s : State) (h : RawWindowPre p s) :
    WP isa (.block VG.Impl.Rsa.AArch64.WindowShared.guard) s (GuardPre p) := by
  obtain ⟨mi,X,Xc,v,hc,ht,hy,hw,hw',hv,hn⟩ := h
  refine WP.mono (BlockedRedc.guard_ok hc.good.scr hc.good.x0 hc.good.hdr (Nat.le_refl _) (by omega))
    fun t ⟨⟨hm,h3,h4⟩,kt⟩ => ?_
  have hf : Frm (off p.B p.o) (crtWinRanges p.wx) s.mem t.mem := by rw [hm]; exact Frm.refl _ _ _
  exact ⟨⟨mi,X,Xc,v,hc.of_win hf kt.wr (kt.gpr .x0 (by decide)),hm ▸ ht,hm ▸ hy,hw,hw',hv,hm ▸ hn⟩,h3,h4⟩

theorem guard_fast {p : XPub} {s : State} (h : GuardPre p s)
    (h3 : isa.eval (.nonzero .x .x3) s = some true)
    (h4 : isa.eval (.zero .x .x4) s = some true) : FastPre p s := by
  obtain ⟨mi,X,Xc,v,hc,ht,hy,hw,hw',hv,hn⟩ := h.raw
  rw [eval_nonzero,h.width,ne_zero_iff,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show p.wx/16 < 2^64 by omega)] at h3
  rw [eval_zero,h.rem,eq_zero_iff,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show p.wx%8 < 2^64 by omega)] at h4
  have hh3 := of_decide_eq_true (Option.some.inj h3)
  have hh4 := of_decide_eq_true (Option.some.inj h4)
  exact ⟨mi,X,Xc,v,hc,ht,by omega,hw',hh4,hv,hn⟩

theorem code_ct : RelCT isa (Two RawWindowPre) code (fun _ _ => True) := by
  unfold code VG.Impl.Rsa.AArch64.WindowShared.code
  refine RelCT.seq (two_piece [.x0]
    (pins_x0B (fun p : XPub => off p.B p.o) (fun _ _ ⟨_,_,_,_,hc,_⟩ => hc.good.x0))
    (by taint_decide) guard_post) ?_
  refine two_ite (Φ := GuardPre) ?_ ?_ ?_
  · intro p s t hs ht
    rw [eval_nonzero,eval_nonzero,hs.width,ht.width]
  · refine two_ite ?_ ?_ ?_
    · intro p s t hs ht
      rw [eval_zero,eval_zero,hs.1.rem,ht.1.rem]
    · exact two_map id (fun _ _ h => guard_fast h.1.1 h.1.2 h.2) fast_ct
    · exact two_map id (fun _ _ h => h.1.1.raw)
        (WindowFive.windowBody_raw_ct Mont.productEight WindowVector.selector)
  · exact two_map id (fun _ _ h => h.1.raw)
      (WindowFive.windowBody_raw_ct Mont.productEight WindowVector.selector)

theorem fn_ct : ConstantTime isa WindowHelper.fnContract.pre WindowHelper.fnContract.pub code := by
  apply RelCT.constantTime (code_ct.mono ?_ (fun _ _ h => h))
  rintro s t ⟨hs,ht,hsp,h0,h1,hw⟩
  refine ⟨⟨s.gpr .x0,(s.gpr .x1).toNat*8,0,0,Proof.Rsa.Mont.wOf s.mem (s.gpr .x0)⟩,
    WindowHelper.fn_context hs,?_,hsp⟩
  rw [hw,h0,h1]
  exact WindowHelper.fn_context ht

theorem verified : Verified target code (Proof.Rsa.MontWindow.windowContract abi) :=
  Verified.of_correct fn_correct fn_ct WindowHelper.fn_implies

end VG.Proof.Bignum.AArch64.WindowShared
