module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuildCT
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowReset
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuildCT
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowReset
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Math
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.CrtMath

/-! The wider-table initializer shares only workspace and source layout between runs. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt (ldw)
open VG.Proof.MlKem.AArch64 (Keep)

def EPreWide (sp sl : Nat) (a : BPub) (s : State) : Prop :=
  EPre sp sl a s ∧ a.x.o + slot a.x.wx 8 + CrtWindowFive.tabBytes32 a.x.wx ≤ a.x.Z

theorem expInit_tpre {sp sl : Nat} {a : BPub} {s : State} (h : EPreWide sp sl a s) :
    WP isa (VG.Impl.Rsa.AArch64.WindowFive.expInit sp sl) s (TPre a.x) := by
  obtain ⟨h,hwide⟩ := h
  obtain ⟨minv, X, x, y, eb, hc, hw2, hwx, hw30, hn, hinv, hodd, hxl, -, hyl, -, hsp, hsl, hep, hel, -⟩ := h
  have hT : Scr s (off a.x.B a.x.o) (slot a.x.wx 8 + CrtWindowFive.tabBytes32 a.x.wx) :=
    hc.scr.sub (by omega) (by unfold slot hdrBytes; omega)
  have hPn := hT.nowrap
  have hY0 := slot_le (w := a.x.wx) (show aY < 8 by decide)
  have hY1 := hdr_lt_slot a.x.wx aY (show 31 < 32 by decide)
  have hc₀ : TableCtx s (off a.x.B a.x.o) a.x.wx minv X (wv s.mem (off a.x.B a.x.o) (slot a.x.wx Crt.aXc) a.x.wx) :=
    ⟨hc.good, hT, hn, hinv, rfl⟩
  refine WP.mono (crtExpInit_ok hc hsp hsl hep hel) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := writeW_outside s.mem (off a.x.B a.x.o) (d := 8 * Crt.sExp) a.ptr (by decide)
  have o2 := writeW_outside (s.mem.writeW (off (off a.x.B a.x.o) (8 * Crt.sExp)) a.ptr) (off a.x.B a.x.o)
    (d := 8 * Crt.sExpLen) (BitVec.ofNat 64 eb.length) (by decide)
  have o3 := writeW_outside ((s.mem.writeW (off (off a.x.B a.x.o) (8 * Crt.sExp)) a.ptr).writeW
    (off (off a.x.B a.x.o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 eb.length)) (off a.x.B a.x.o) (d := 8 * Crt.sI)
    (BitVec.ofNat 64 0) (by decide)
  rw [← hm₁] at o3
  have f₁ : Frm (off a.x.B a.x.o) (CrtWindowFive.crtExpRanges a.x.wx) s.mem t₁.mem :=
    ((Frm.of_outside o1 (by simp [CrtWindowFive.crtExpRanges])).trans (Frm.of_outside o2 (by simp [CrtWindowFive.crtExpRanges]))).trans
      (Frm.of_outside o3 (by simp [CrtWindowFive.crtExpRanges]))
  refine ⟨minv, X, _, hc₀.of_frm f₁ k₁.wr (k₁.gpr .x0 (by decide)), hxl, ?_, hw2, by omega_arith,
    VG.Proof.Bignum.coprime_pow2 hodd _⟩
  rw [o3.wv (by unfold Crt.sI sFn at *; omega_arith) (by omega_arith), o2.wv (by unfold Crt.sExpLen sFn at *; omega_arith)
    (by omega_arith), o1.wv (by unfold Crt.sExp sFn at *; omega_arith) (by omega_arith)]
  exact hyl


theorem expInit_ct {sp sl : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0,.x5]) (.block [ldw .x3 .x5 sp,sth .x3 Crt.sExp,
      ldw .x3 .x5 sl,sth .x3 Crt.sExpLen,movi .x3 0,sth .x3 Crt.sI]) hc).isSome = true) :
    RelCT isa (Two (EPreWide sp sl)) (VG.Impl.Rsa.AArch64.WindowFive.expInit sp sl) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.expInit
  exact RelCT.block_append (l₁ := ([ldh .x5 Crt.sLink] : List Instr))
    (RelCT.seq (two_piece (Ψ := fun (a : BPub) t => t.gpr .x0 = off a.x.B a.x.o ∧ t.gpr .x5 = a.x.B) [.x0]
      (pins_x0B (fun a : BPub => off a.x.B a.x.o) fun a s (h : EPreWide sp sl a s) =>
        let ⟨_,_,_,_,_,ctx,_⟩ := h.1; ctx.x0) (by taint_decide)
      fun _ _ h => crtLink_ok h.1)
    (two_taint [.x0,.x5] (pins_of (fun a r => if r = .x0 then off a.x.B a.x.o else a.x.B)
      fun a s h r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) hT))

theorem expHead_ct (M : Mont) {sp sl : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0,.x5]) (.block [ldw .x3 .x5 sp,sth .x3 Crt.sExp,
      ldw .x3 .x5 sl,sth .x3 Crt.sExpLen,movi .x3 0,sth .x3 Crt.sI]) hc).isSome = true) :
    RelCT isa (Two (EPreWide sp sl)) (VG.Impl.Rsa.AArch64.WindowFive.expHead M.mm sp sl) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.expHead
  refine RelCT.seq (two_post (Ψ := fun a s => TPre a.x s) (expInit_ct hT)
    (fun _ _ h => expInit_tpre h)) ?_
  refine RelCT.seq (two_map (fun a : BPub => a.x) (fun _ _ h => h)
    (two_post (Ψ := fun (p : XPub) s => s.gpr .x0 = off p.B p.o) (tabBuild_ct M) ?_)) ?_
  · rintro p s ⟨mi,X,Xc,hctx,hxl,hyl,hw,hw',hR⟩
    exact WP.mono (tabBuild_ok M hctx hw hw' hR hxl (Q := False) (x := 0) False.elim hyl False.elim)
      fun t ⟨ct,_⟩ => ct.good.x0
  · exact two_map (fun p : XPub => off p.B p.o) (fun _ _ h => h) resetWindow_ct

end VG.Proof.Bignum.AArch64.WindowFive
