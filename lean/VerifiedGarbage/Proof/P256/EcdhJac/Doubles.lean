import VerifiedGarbage.Proof.P256.EcdhJac.Counter
import VerifiedGarbage.Proof.P256.EcdhJac.HotField

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem double_state (hC : Law C) (ha : AM3 C) {base : Addr} {P Q : Point C} {k : Nat}
    (hQ : onCurve C Q=true) {s : State} (hs : RState base P Q k s) :
    WP isa Impl.P256.EcdhJac.double s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧ RState base P (add Q Q) k t := by
  exact WP.mono (double_ok hC ha hs.field hQ hs.point) fun t ⟨kt,hi,hp⟩ =>
    ⟨kt,hs.next (kt.widenRegs allocated_regs) hi hp⟩

theorem doubles_ok (hC : Law C) (ha : AM3 C) {base : Addr} {P Q : Point C} {k j : Nat}
    (hQ : onCurve C Q=true) (hj : j<52) {s : State} (hs : RState base P Q k s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa Impl.P256.EcdhJac.dbls s fun t =>
      Frame base work s t ∧ RState base P (mul 32 Q) k t ∧ t.gpr .x19=BitVec.ofNat 64 j := by
  unfold Impl.P256.EcdhJac.dbls
  apply WP.seq
  refine WP.mono (doubleCounter_start s h19) fun a ⟨a19,ka⟩ => ?_
  have fa : Frame base work s a := (AllocatedFrame.of_keeps ka).widenRegs (by decide)
  have ca := hs.of_keeps ka (by decide)
  let I := fun q t => Frame base work s t ∧ RState base P (mul (2^(5-q)) Q) k t ∧
    t.gpr .x19=BitVec.ofNat 64 (2048*q+j)
  apply countRegLoop_ok .x4 (Inv:=I) (n:=5) (by decide)
  · intro q b hq hq5 hi
    obtain ⟨fb,cb,b19⟩ := hi
    unfold Impl.P256.EcdhJac.dblStep
    apply WP.seq
    refine WP.mono (double_state hC ha (hC.onCurve_mul hQ _) cb) fun d ⟨fd,cd⟩ => ?_
    have d19 := (fd.regs.gpr .x19 allocatedRegs_x19).trans b19
    refine WP.mono (doubleCounter_ok d hq hq5 hj d19) fun t ⟨t19,t4,kt⟩ => ?_
    have ft : Frame base work d t := (AllocatedFrame.of_keeps kt).widenRegs (by decide)
    have ct := cd.of_keeps kt (by decide)
    have ep : add (mul (2^(5-q)) Q) (mul (2^(5-q)) Q)=mul (2^(5-(q-1))) Q := by
      rw [hC.add_mul_mul hQ,show 5-(q-1)=(5-q)+1 by omega,Nat.pow_succ]
      congr 1
      omega
    rw [ep] at ct
    exact ⟨⟨(fb.trans (fd.widenRegs allocated_regs)).trans ft,ct,t19⟩,t4⟩
  · intro t ht
    obtain ⟨ft,ct,t19⟩ := ht
    exact ⟨ft,ct,by simpa only [Nat.mul_zero,Nat.zero_add] using t19⟩
  · decide
  · refine ⟨fa,?_,a19⟩
    simpa only [Nat.sub_self,Nat.pow_zero,mul_one_pt] using ca

end VG.Proof.P256.EcdhJac
