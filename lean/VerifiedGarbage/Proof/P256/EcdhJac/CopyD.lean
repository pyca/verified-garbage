import VerifiedGarbage.Proof.P256.EcdhJac.BuildStart

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem copyD_ok {base : Addr} {P Q : Point C} {k : Nat} {s : State}
    (hf : Fixed base P k s) (hp : JPt base s selectedSlot Q)
    (hd : InvJ C (tmv C 4 base s K.S.t3) (tmv C 4 base s K.S.t2) (tmv C 4 base s K.E.z) P)
    (hx : wordsVal s.mem base K.S.t3 4<C.p) (hy : wordsVal s.mem base K.S.t2 4<C.p) :
    WP isa (.block (copy 4 K.D.x K.S.t3++copy 4 K.D.y K.S.t2)) s fun t =>
      Frame base work s t ∧ JPt base t selectedSlot Q ∧
      (∀x∈[K.D.x,K.D.y],wordsVal t.mem base x 4<C.p) ∧
      InvJ C (tmv C 4 base t K.D.x) (tmv C 4 base t K.D.y) (tmv C 4 base t K.E.z) P := by
  have hi : Inv M base 8192 C.p Sl [K.S.t3,K.S.t2] (tmv C 4 base s) s :=
    ⟨hf.field.scr,hf.field.mod,by decide,fun x hh => by
      rcases List.mem_cons.mp hh with rfl|hh
      · exact hx
      · rw [List.mem_singleton.mp hh]; exact hy,fun _ _ => rfl⟩
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok layout aligned hi (o:=K.D.x) (a:=K.S.t3) (by decide) (by decide))
    fun a ⟨ka,ia⟩ => ?_
  refine WP.mono (copyField_ok layout aligned ia (o:=K.D.y) (a:=K.S.t2) (by decide) (by decide))
    fun t ⟨kt,it⟩ => ?_
  have fr := (opFrame (by decide) ka).trans (opFrame (by decide) kt)
  have un : Unch base [(608,32),(640,32),(128,32)] s.mem t.mem := by
    intro x hh
    exact (kt.mem x (hh (640,32) (by simp)) (hh (128,32) (by simp))).trans
      (ka.mem x (hh (608,32) (by simp)) (hh (128,32) (by simp)))
  have sel : ∀i<5,wordsVal t.mem base (selectedSlot i) 4=wordsVal s.mem base (selectedSlot i) 4 := by
    intro i hi
    exact un.wordsVal ((show ∀i<5,∀w∈[(608,32),(640,32),(128,32)],selectedSlot i+32≤w.1 ∨ w.1+w.2≤selectedSlot i from by decide +kernel) i hi)
      (by unfold selectedSlot; split <;> omega)
  have vx := it.val K.D.x (by decide)
  have vy := it.val K.D.y (by decide)
  change tmv C 4 base t 608=_ at vx
  change tmv C 4 base t 640=_ at vy
  simp only [show K.D.x=608 from rfl,show K.D.y=640 from rfl,
    show K.S.t3=896 from rfl,show K.S.t2=864 from rfl,
    Function.update_apply,Nat.reduceEqDiff,ite_true,ite_false] at vx vy
  refine ⟨fr,hp.congr sel,fun x hh => it.lt x ?_,?_⟩
  · rcases List.mem_cons.mp hh with rfl|hh
    · decide
    · rw [List.mem_singleton.mp hh]; decide
  · change InvJ C (tmv C 4 base t 608) (tmv C 4 base t 640) (tmv C 4 base t 768) P
    have vz : tmv C 4 base t 768=tmv C 4 base s 768 := by
      simpa only [selectedSlot,show 2<3 from by decide,ite_true,Nat.reduceMul,Nat.reduceAdd]
        using congrArg (fun x => toM C.p (2^(64*4)) x) (sel 2 (by decide))
    rw [vx,vy,vz]
    exact hd

end VG.Proof.P256.EcdhJac
