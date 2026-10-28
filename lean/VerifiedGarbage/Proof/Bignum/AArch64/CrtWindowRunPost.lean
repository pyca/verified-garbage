module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunContext
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTails
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailLoop
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroups
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupLoop
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoopControl
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

/-! Functional postconditions used to carry the constant-time loop invariants. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (groupBody tailBody haveFive remaining expGroups expTail)

theorem RunInv.groupStep (W : Window) {p : RunPub} {i : Nat} {t : State}
    (h : RunInv p i 0 t) (hi : i+5 ≤ p.len) :
    WP isa (groupBody W.code) t fun u => RunInv p (i+5) 0 u ∧
      u.gpr .x9 = if i+10 ≤ p.len then 1 else 0 := by
  obtain ⟨s,mi,X,Xc,bs,hI,hw,hw',hR,hL,hL',hr,hb,ho⟩ := h
  refine WP.mono (groupBody_ok W hw hw' hR (by omega) (by omega) hr hb ho hI)
    fun u ⟨hu,h9⟩ => ?_
  exact ⟨⟨s,mi,X,Xc,bs,hu,hw,hw',hR,hL,hL',hr,hb,ho⟩,by simpa only [hL] using h9⟩

theorem RunInv.tailStep (W : Window) {p : RunPub} {i b : Nat} {t : State}
    (h : RunInv p i b t) (hi : i < p.len) :
    WP isa (tailBody W.code) t fun u => RunInv p (i+1) ((b+8)%5) u ∧
      u.gpr .x3 = BitVec.ofNat 64 (p.len-(i+1)) := by
  obtain ⟨s,mi,X,Xc,bs,hI,hw,hw',hR,hL,hL',hr,hb,ho⟩ := h
  refine WP.mono (tailBody_ok W hw hw' hR (by omega) hr hb ho hI) fun u ⟨hu,h3⟩ => ?_
  exact ⟨⟨s,mi,X,Xc,bs,hu,hw,hw',hR,hL,hL',hr,hb,ho⟩,by simpa only [hL] using h3⟩

theorem RunInv.haveFive {p : RunPub} {i b : Nat} {t : State}
    (h : RunInv p i b t) (hi : i ≤ p.len) :
    WP isa (.block haveFive) t fun u => RunInv p i b u ∧
      u.gpr .x9 = if i+5 ≤ p.len then 1 else 0 := by
  obtain ⟨s,mi,X,Xc,bs,hI,hw,hw',hR,hL,hL',hr,hb,ho⟩ := h
  refine WP.mono (haveFive_ok hI.ctx hi hL' hI.idx (hL ▸ hI.len)) fun u ⟨⟨hm,h9⟩,ku⟩ => ?_
  exact ⟨⟨s,mi,X,Xc,bs,hI.keepMem hm ku (by decide) (by decide),hw,hw',hR,hL,hL',hr,hb,ho⟩,h9⟩

theorem RunInv.remaining {p : RunPub} {i b : Nat} {t : State}
    (h : RunInv p i b t) (hi : i ≤ p.len) :
    WP isa (.block remaining) t fun u => RunInv p i b u ∧ u.gpr .x3 = BitVec.ofNat 64 (p.len-i) := by
  obtain ⟨s,mi,X,Xc,bs,hI,hw,hw',hR,hL,hL',hr,hb,ho⟩ := h
  refine WP.mono (remaining_ok hI.ctx hi hI.idx (hL ▸ hI.len)) fun u ⟨⟨hm,h3⟩,ku⟩ => ?_
  exact ⟨⟨s,mi,X,Xc,bs,hI.keepMem hm ku (by decide) (by decide),hw,hw',hR,hL,hL',hr,hb,ho⟩,h3⟩

theorem RunInv.groups (W : Window) {p : RunPub} {t : State} (h : RunInv p 0 0 t) :
    WP isa (expGroups W.code) t (RunInv p (5*(p.len/5)) 0) := by
  obtain ⟨s,mi,X,Xc,bs,hI,hw,hw',hR,hL,hL',hr,hb,ho⟩ := h
  refine WP.mono (expGroups_ok W hw hw' hR (by omega) hr hb ho hI) fun u hu => ?_
  exact ⟨s,mi,X,Xc,bs,by simpa only [hL] using hu,hw,hw',hR,hL,hL',hr,hb,ho⟩

theorem RunInv.tails (W : Window) {p : RunPub} {i : Nat} {t : State}
    (h : RunInv p i 0 t) (hi : i ≤ p.len) :
    WP isa (expTail W.code) t (RunInv p p.len ((8*(p.len-i))%5)) := by
  obtain ⟨s,mi,X,Xc,bs,hI,hw,hw',hR,hL,hL',hr,hb,ho⟩ := h
  refine WP.mono (expTail_ok W hw hw' hR (by omega) (by omega) hr hb ho hI) fun u hu => ?_
  exact ⟨s,mi,X,Xc,bs,by simpa only [hL] using hu,hw,hw',hR,hL,hL',hr,hb,ho⟩

end VG.Proof.Bignum.AArch64.WindowFive
