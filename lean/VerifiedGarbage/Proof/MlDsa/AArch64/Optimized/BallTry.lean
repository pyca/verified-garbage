import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.BallLoop
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ball

/-! A parser step independent of its byte budget or buffer location. The
second SHAKE block can therefore resume exactly the first block's state. -/
namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (IPoly q n)
open VG.Proof.MlDsa.AArch64.Sample.Ball (CStored set_ok)
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (lt_bit)
open VG.Impl.MlDsa.AArch64.Sample (bTry)

abbrev tryRegs : List Reg := [.x6,.x7,.x8,.x9,.x10,.x11,.x13,.x14]

structure TryPost (τ : Nat) (signs : Array Bool) (a : Addr) (c : IPoly) (i : Nat)
    (j : Byte) (s u : State) : Prop where
  keep : Keep tryRegs s u
  frame : Frame [polyR a] s.mem u.mem
  x9 : u.gpr .x9 = s.gpr .x9 >>> ((bStep τ signs (c,i) j).2-i)
  x10 : (u.gpr .x10).toNat = (bStep τ signs (c,i) j).2
  x11 : (u.gpr .x11).toNat = 256-(bStep τ signs (c,i) j).2
  stored : CStored u.mem a (bStep τ signs (c,i) j).1

theorem try_ok {τ i : Nat} {signs : Array Bool} {a : Addr} {c : IPoly} {j : Byte} {s : State}
    (hi : i < 256) (h26 : s.gpr .x26 = a)
    (h9 : (s.gpr .x9).getLsbD 0 = signs.getD (i+τ-256) false)
    (h10 : (s.gpr .x10).toNat = i) (h11 : (s.gpr .x11).toNat = 256-i)
    (h12 : (s.gpr .x12).toNat = q-2) (h15 : (s.gpr .x15).toNat = 1)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x2) 1) (hb : s.mem (s.gpr .x2) = j)
    (hw : ∀ k < 256, InRegions s.wr (coeffAddr a k) 4) (hst : CStored s.mem a c) :
    WP isa bTry s (TryPost τ signs a c i j s) := by
  refine WP.seq (wp_ldrb (a := s.gpr .x2) (by decide) (ptr_zero _) hin fun s₁ o₁ e₁ =>
    wp_sub fun s₂ o₂ e₂ => wp_lsr (by decide) fun s₃ o₃ e₃ => wp_nil ?_)
  have k₃ := ((o₁.keep.trans o₂.keep).trans o₃.keep).mono (rs' := [.x6,.x7]) (by decide)
  have m₃ : s₃.mem = s.mem := by rw [o₃.mem,o₂.mem,o₁.mem]
  have v6 : (s₃.gpr .x6).toNat = j.toNat := by rw [o₃.get .x6,o₂.get .x6,e₁,toNat_byte,hb]
  have v7 : (s₃.gpr .x7).toNat = if i<j.toNat then 1 else 0 := by
    rw [e₃,e₂,o₁.get .x10]
    exact lt_bit h10 (by rw [e₁,toNat_byte,hb]) (by omega) (by have := j.isLt; omega)
  by_cases hr : i<j.toNat
  · have hstep : bStep τ signs (c,i) j = (c,i) := by
      unfold bStep; rw [ifT (show i<n by exact hi),ifT hr]
    refine WP.ite true (by rw [eval_nonzero,ne_zero_iff,v7,ifT hr]; rfl)
      (fun _ => wp_nil ?_) (fun h => nomatch h)
    refine ⟨k₃.mono (by decide), ?_, ?_, ?_, ?_, ?_⟩
    · rw [m₃]; exact Frame.refl _ _
    · rw [hstep,Nat.sub_self,BitVec.ushiftRight_zero]; exact k₃.get .x9
    · rw [hstep,k₃.get .x10]; exact h10
    · rw [hstep,k₃.get .x11]; exact h11
    · rw [hstep,m₃]; exact hst
  · have hstep : bStep τ signs (c,i) j =
        ((c.set! i c[j.toNat]!).set! j.toNat (if signs.getD (i+τ-256) false then -1 else 1),i+1) := by
      unfold bStep; rw [ifT (show i<n by exact hi),ifF hr]
    refine WP.ite false (by rw [eval_nonzero,ne_zero_iff,v7,ifF hr]; rfl)
      (fun h => nomatch h) (fun _ => WP.mono (set_ok (aP := a) (c := c) (i := i) (j := j.toNat) (by omega) hi
        (by rw [k₃.get .x26,h26]) v6 (by rw [k₃.get .x10,h10])
        (by rw [k₃.get .x11,h11]) (by rw [k₃.get .x12,h12]) (by rw [k₃.get .x15,h15])
        (by rw [k₃.wr]; exact hw) (by rw [m₃]; exact hst)) fun u ⟨ku,hu10,hu11,hu9,hcu,hfu⟩ => ?_)
    refine ⟨(k₃.trans ku).mono (by decide), ?_, ?_, ?_, ?_, ?_⟩
    · rw [← m₃]; exact hfu
    · rw [hstep,show i+1-i=1 by omega,hu9,k₃.get .x9]
    · rw [hstep]; exact hu10
    · rw [hstep]; exact hu11
    · rw [hstep]; rw [k₃.get .x9,h9] at hcu; exact hcu
end VG.Proof.MlDsa.AArch64.Optimized.Ball
