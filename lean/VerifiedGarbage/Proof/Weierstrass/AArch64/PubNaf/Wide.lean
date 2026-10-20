module
public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNafWide
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.PrepTiming
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WidePrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
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

/-- A signed byte stores every digit exactly: width seven's magnitude is at most63. -/
theorem digit_bounds {w : Nat} (hw : FastNaf.Width w) (k j : Nat) :
 FastNaf.magnitude w k j≤2^(w-1)-1 ∧
 (FastNaf.byte w k j).toInt=FastNaf.digit w k j := by
 refine ⟨FastNaf.magnitude_le hw k j,?_⟩
 have hb:=fastMagnitude_bound w k j
 have hd:=fastDigit_eq w k j
 have hr : -128≤FastNaf.digit w k j ∧ FastNaf.digit w k j<128 := by
  rw [hd]; split <;> omega
 have he : FastNaf.byte w k j=BitVec.ofInt 8 (FastNaf.digit w k j) := by
  by_cases h : w=7 <;> simp only [FastNaf.byte,FastNaf.digit,h,ite_true,ite_false,FastNaf7.byte,Naf5.byte]
 rw [he]
 exact BitVec.toInt_ofInt_eq_self (by decide) hr.1 hr.2
/-- Timing certificates depend only on public registers, for either fixed width. -/
structure TimingChecks (K : WinCfg) (src w : Nat) : Prop where
 init : ConstantTime isa (fun _=>True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
  (.block (if w=7 then Impl.Weierstrass.AArch64.PubNafWide.prepInit7 K src else Impl.Weierstrass.AArch64.PubNaf.prepInit K src))
 step : ConstantTime isa (fun _=>True) (AArch64.Taint.Agree (Taint.ofRegs (prepPublic K.M.n)))
  (Impl.Weierstrass.AArch64.PubNaf.prepStep K.M.n)

theorem prep_relCT (K : WinCfg) {w : Nat} (hw : FastNaf.Width w) (hR : Regs K.M.n)
 {base : Addr} {size src : Nat} (hsrc : src+8*K.M.n≤size) (hsrc8 : src%8=0)
 (hbits : K.bits<4096) (hb : K.bits+(64*K.M.n+1)≤size) (hc : TimingChecks K src w) :
 RelCT isa (fun s t=>Scr s base size ∧ Scr t base size ∧ s.sp=t.sp ∧
   wordsVal s.mem base src K.M.n=wordsVal t.mem base src K.M.n)
  (Impl.Weierstrass.AArch64.PubNafWide.prep K src w) (fun _ _=>True) := by
 rcases hw with rfl|rfl
 · exact PubNaf.prep_relCT K hR hsrc hsrc8 hbits hb ⟨hc.init,hc.step⟩
 · exact prep7_relCT K hR hsrc hsrc8 hbits hb ⟨hc.init,hc.step⟩

end VG.Proof.Weierstrass.AArch64.PubNafWide
