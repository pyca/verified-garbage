import VerifiedGarbage.Proof.P256.EcdhJac.HotField
import VerifiedGarbage.Proof.P256.EcdhJac.Entry

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

def addLive : List Nat := [608,640,672]++selected++live

 theorem EntryPost.rstate {base : Addr} {P Q : Point C} {k j : Nat} {s t : State}
    (h : EntryPost base P k j live s t) (hs : RState base P Q k s) : RState base P Q k t := by
  have hp : ∀x∈live,tmv C 4 base t x=tmv C 4 base s x := by
    intro x hx; unfold tmv; rw [h.same x hx]
  refine ⟨hs.fixed.keep (frame_build h.frame),hs.table.keep h.frame,
    h.field.sub (fun _ hx => List.mem_append_right _ hx),?_⟩
  rw [hp _ (by decide),hp _ (by decide),hp _ (by decide)]
  exact hs.point

structure AddPost (base : Addr) (P Q : Point C) (k : Nat) (s t : State) : Prop where
  frame : AllocatedFrame allocatedRegs base work s t
  state : RState base P Q k t
  field : Inv M base 8192 C.p Sl addLive (tmv C 4 base t) t
  same : ∀x∈selected++live,tmv C 4 base t x=tmv C 4 base s x
  point : (tmv C 4 base t K.D.x,tmv C 4 base t K.D.y,tmv C 4 base t K.D.z)=
    jacAddF (tmv C 4 base t K.R.x) (tmv C 4 base t K.R.y) (tmv C 4 base t K.R.z)
      (tmv C 4 base t K.E.x) (tmv C 4 base t K.E.y) (tmv C 4 base t K.E.z)

theorem add_state {base : Addr} {P Q : Point C} {k : Nat} {s : State}
    (hs : RState base P Q k s)
    (hi : Inv M base 8192 C.p Sl (selected++live) (tmv C 4 base s) s)
    (h2 : tmv C 4 base s 5400=tmv C 4 base s 768*tmv C 4 base s 768)
    (h3 : tmv C 4 base s 5432=tmv C 4 base s 768*(tmv C 4 base s 768*tmv C 4 base s 768)) :
    WP isa Impl.P256.EcdhJac.add s (AddPost base P Q k s) := by
  refine WP.mono (add_ok hi (by decide) h2 h3) fun t ⟨kt,it,hp⟩ => ?_
  have same : ∀x∈selected++live,tmv C 4 base t x=tmv C 4 base s x := by
    intro x hx
    have hv := it.val x (List.mem_append_right _ hx)
    change tmv C 4 base t x=_ at hv
    rw [hv]
    apply runOps_of_not_out
    have hn : ∀op∈CachedField.head++CachedField.tail,∀x∈selected++live,op.out≠x := by decide
    exact fun op hop => hn op hop x hx
  have state : RState base P Q k t := by
    refine ⟨hs.fixed.keep (frame_build (kt.widenRegs allocated_regs)),
      hs.table.keep (kt.widenRegs allocated_regs),it.to_tmv.sub (by decide),?_⟩
    rw [same _ (by decide),same _ (by decide),same _ (by decide)]
    exact hs.point
  refine ⟨kt,state,it.to_tmv,same,?_⟩
  have vx := it.val K.D.x (by decide)
  have vy := it.val K.D.y (by decide)
  have vz := it.val K.D.z (by decide)
  change tmv C 4 base t K.D.x=_ at vx
  change tmv C 4 base t K.D.y=_ at vy
  change tmv C 4 base t K.D.z=_ at vz
  rw [vx,vy,vz,hp,same _ (by decide),same _ (by decide),same _ (by decide),
    same _ (by decide),same _ (by decide),same _ (by decide)]

end VG.Proof.P256.EcdhJac
