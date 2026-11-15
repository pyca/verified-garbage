module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStepCT
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcGuard
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStepCT
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Select SIMD only for complete public-width tiles, with a scalar fallback:
for a table of 16 or 32 entries (`select_ok`, `select_ct`), and RSA's of 32
with its scalar selector (`selector`). -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff eval_zero eq_zero_iff)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx Selector)

def selected : Prog isa := VG.Impl.Rsa.AArch64.WindowSelectVector.select 32 Selector.scalar.code

/-! ## RSA's table of 32 entries -/

theorem selected_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hv : v < 32)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hN : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa selected s fun t => TableCtx t P w mi X Xc ∧
      wv t.mem P (slot w Crt.aT) w = wv s.mem P (slot w (8 + v)) w ∧
      Frm P (selRanges w) s.mem t.mem ∧ Keep mmRegs s t :=
  WP.mono (select_ok (Or.inr rfl) (fun hu tab nib =>
      WP.mono (Selector.scalar.ok (TableCtx.ofC hu) hw hw' hv tab nib) fun _ ⟨ct,hy,hf,kt⟩ => ⟨ct.toC,hy,hf,kt⟩)
    hc.toC hw' hv ht hN) fun _ ⟨ct,hy,hf,kt⟩ => ⟨TableCtx.ofC ct,hy,hf,kt⟩

theorem selP_n {p : XPub} {s : State} (h : VG.Proof.Bignum.AArch64.WindowFive.SelP p s) : SelPn 32 p s := by
  obtain ⟨mi,X,Xc,v,hc,h⟩ := h
  exact ⟨mi,X,Xc,v,hc.toC,h⟩

theorem selP_of_n {p : XPub} {s : State} (h : SelPn 32 p s) : VG.Proof.Bignum.AArch64.WindowFive.SelP p s := by
  obtain ⟨mi,X,Xc,v,hc,h⟩ := h
  exact ⟨mi,X,Xc,v,TableCtx.ofC hc,h⟩

/-- `BlockPreN` for RSA's table of 32 entries. -/
def BlockPre (p : XPub) (s : State) : Prop := VG.Proof.Bignum.AArch64.WindowFive.SelP p s ∧ 8 ≤ p.wx

theorem blocked_ct : RelCT isa (Two BlockPre)
    (VG.Impl.Rsa.AArch64.WindowSelectVector.blocked 32) (fun _ _ => True) :=
  two_map id (fun _ _ ⟨⟨mi, X, Xc, v, hc, h⟩, hw⟩ => ⟨⟨mi, X, Xc, v, hc.toC, h⟩, hw⟩) (blockedN_ct (Or.inr rfl))

theorem selected_ct : RelCT isa (Two VG.Proof.Bignum.AArch64.WindowFive.SelP)
    selected (fun _ _ => True) :=
  two_map id (fun _ _ h => selP_n h)
    (select_ct (Or.inr rfl) (two_map id (fun _ _ h => selP_of_n h) Selector.scalar.ct))

def selector : Selector := ⟨selected,selected_ok,selected_ct⟩

end VG.Proof.Bignum.AArch64.WindowVector
