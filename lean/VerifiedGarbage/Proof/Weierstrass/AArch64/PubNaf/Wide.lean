module
public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNafWide
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.PrepTiming
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WidePrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
import VerifiedGarbage.Proof.Framework.PlainSimp
@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.PubNafWide
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Impl.Mont VG.Impl.Mont.AArch64

/-- Both public widths write all digits, preserving every other scratch byte. -/
theorem prep_ok (K : WinCfg) {w : Nat} (hw : FastNaf.Width w) (hR : Regs K.M.n)
 {s : State} {base : Addr} {size src : Nat} (hs : Scr s base size)
 (hsrc : src+8*K.M.n≤size) (hsrc8 : src%8=0) (hbits : K.bits<4096)
 (hb : K.bits+(64*K.M.n+1)≤size) :
 WP isa (Impl.Weierstrass.AArch64.PubNafWide.prep K src w) s fun t=>
  Scr t base size ∧ t.gpr .x19=0 ∧
  (∀i<64*K.M.n+1,t.mem (off base (K.bits+i))=FastNaf.byte w (wordsVal s.mem base src K.M.n) i) ∧
  KeepRegs (clobs K.M.n) s t ∧ Outside base K.bits (64*K.M.n+1) s.mem t.mem := by
 rcases hw with rfl|rfl
 · refine WP.mono (PubNaf.prep_ok K hR hs hsrc hsrc8 hbits hb) fun t ⟨h,k,o⟩=>?_
   exact ⟨h.scr,by rw [h.count,Nat.sub_self]; rfl,h.digits,k,o⟩
 · refine WP.mono (prep7_ok K hR hs hsrc hsrc8 hbits hb) fun t ⟨h,k,o⟩=>?_
   exact ⟨h.scr,by rw [h.count,Nat.sub_self]; rfl,h.digits,k,o⟩

end VG.Proof.Weierstrass.AArch64.PubNafWide
