import VerifiedGarbage.Proof.P256.EcdhJac.WindowPost
import VerifiedGarbage.Proof.P256.EcdhJac.Extra

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

def wrappedWrites : List (Nat×Nat) := buildWork++[(7800,40)]
def wrappedRegs : List Reg := regs.filter fun r=>r∉extraRegs

structure WrappedPost (base : Addr) (P : Point C) (k : Nat) (s t : State) : Prop where
  frame : AllocatedFrame wrappedRegs base wrappedWrites s t
  field : Inv M base 8192 C.p Sl live (tmv C 4 base t) t
  point : 1≤k → k<C.n → Rep C (tmv C 4 base t K.R.x)
    (tmv C 4 base t K.R.y) (tmv C 4 base t K.R.z) (mul k P)
  restored : ∀ r∈extraRegs,t.gpr r=s.gpr r

theorem wrapped_ok {base : Addr} {P : Point C} {k : Nat} {s : State}
    (hf : Fixed base P k s)
    (hwin : ∀ u,Fixed base P k u → WP isa Impl.P256.EcdhJac.window u (WindowPost base P k u)) :
    WP isa Impl.P256.EcdhJac.wrappedWindow s (WrappedPost base P k s) := by
  unfold Impl.P256.EcdhJac.wrappedWindow
  refine WP.seq (WP.mono (saveExtra_ok hf.field.scr (by decide)) fun a ⟨ka,oa,sa⟩=>?_)
  have fa : AllocatedFrame [] base [(7800,40)] s a := ⟨ka,oa.unch⟩
  refine WP.seq (WP.mono (hwin a (hf.keep_save fa)) fun b hb=>?_)
  have sb := savedExtra_keep sa hb.frame.unch (by decide)
  refine WP.mono (restoreExtra_ok hb.field.scr (by decide) sb) fun t ⟨kt,rt⟩=>?_
  have hu : Unch base wrappedWrites s.mem b.mem := (oa.unch.trans hb.frame.unch).mono (by decide)
  refine ⟨⟨restoreExtra_frame ka hb.frame.regs kt rt,fun x hx=>
    (congrFun kt.mem x).trans (hu x hx)⟩,
    (hb.field.of_keeps kt (by decide)).to_tmv,?_,rt⟩
  intro hk hn
  have ht : ∀ x,tmv C 4 base t x=tmv C 4 base b x := fun x=>by unfold tmv; rw [kt.mem]
  rw [ht,ht,ht]
  exact hb.point hk hn

end VG.Proof.P256.EcdhJac
