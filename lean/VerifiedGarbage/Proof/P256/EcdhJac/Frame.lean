import VerifiedGarbage.Proof.P256.EcdhJac.State

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem JPt.congr {base : Addr} {s t : State} {o o' : Nat → Nat} {Q : Point C}
    (h : JPt base s o Q) (he : ∀ i<5,wordsVal t.mem base (o' i) 4=wordsVal s.mem base (o i) 4) :
    JPt base t o' Q := by
  have e : ∀ i<5,tmv C 4 base t (o' i)=tmv C 4 base s (o i) := fun i hi => by
    unfold tmv; rw [he i hi]
  refine ⟨fun i hi => by rw [he i hi]; exact h.lt i hi,?_,?_,?_,?_⟩
  · rw [e 0 (by decide),e 1 (by decide),e 2 (by decide)]; exact h.jac
  · rw [e 2 (by decide)]; exact h.z
  · rw [e 3 (by decide),e 2 (by decide)]; exact h.z2
  · rw [e 4 (by decide),e 3 (by decide),e 2 (by decide)]; exact h.z3

theorem frame_build {base : Addr} {s t : State} (h : Frame base work s t) : Frame base buildWork s t :=
  h.mono (fun _ hr => hr) (fun w hw => ⟨w,List.mem_append_left _ hw,by omega,by omega⟩)

theorem Fixed.keep {base : Addr} {P : Point C} {k : Nat} {s t : State}
    (h : Fixed base P k s) (hk : Frame base buildWork s t) : Fixed base P k t := by
  have hw : ∀ x∈ro,wordsVal t.mem base x 4=wordsVal s.mem base x 4 := by
    intro x hx
    exact hk.unch.wordsVal (by
      have hh : ∀ x∈ro,∀ w∈buildWork,x+32≤w.1 ∨ w.1+w.2≤x := by decide +kernel
      exact hh x hx) (by
      have hh : ∀ x∈ro,x+32≤2^64 := by decide +kernel
      exact hh x hx)
  have hf : ∀ x∈ro,tmv C 4 base t x=tmv C 4 base s x := fun x hx => by unfold tmv; rw [hw x hx]
  refine ⟨⟨hk.scr regs_x0 h.field.scr,h.field.mod.unch hk.unch (by decide +kernel) h.field.scr.nowrap,
    h.field.sl,fun x hx => by change wordsVal t.mem base x 4<C.p; rw [hw x hx]; exact h.field.lt x hx,fun _ _ => rfl⟩,?_,?_,?_,?_⟩
  · rw [hw _ (by decide)]; exact h.zero
  · rw [hf _ (by decide),hf _ (by decide),hf _ (by decide)]; exact h.peer
  · rw [hf _ (by decide)]; exact h.one
  · intro i hi
    rw [hk.unch.byte (by
      intro w hw
      have hh : ∀ w∈buildWork,K.bits+260≤w.1 ∨ w.1+w.2≤K.bits := by decide +kernel
      have := hh w hw; omega) (by change 1824+i+1≤2^64; omega)]
    exact h.bits i hi

theorem TblOk.keep {base : Addr} {P : Point C} {s t : State}
    (h : TblOk base P 16 s) (hk : Frame base work s t) : TblOk base P 16 t := by
  intro a ha ha16
  apply (h a ha ha16).congr
  intro i hi
  exact hk.unch.wordsVal (by
    have hh : ∀ a∈List.range 17,1≤a→∀ i<5,∀ w∈work,entrySlot a i+32≤w.1 ∨ w.1+w.2≤entrySlot a i := by decide +kernel
    exact hh a (List.mem_range.mpr (by omega)) ha i hi) (by unfold entrySlot; omega)

theorem RState.next {base : Addr} {P Q Q' : Point C} {k : Nat} {s t : State}
    (h : RState base P Q k s) (hk : Frame base work s t)
    {E : Nat → Fe C} (hi : Inv M base 8192 C.p Sl live E t)
    (hp : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) Q') : RState base P Q' k t := by
  refine ⟨h.fixed.keep (frame_build hk),h.table.keep hk,hi.to_tmv,?_⟩
  have hv : ∀ x∈live,tmv C 4 base t x=E x := hi.val
  rw [hv _ (by decide),hv _ (by decide),hv _ (by decide)]
  exact hp

end VG.Proof.P256.EcdhJac
