module

public import VerifiedGarbage.Proof.P256.VerifyTable.Field
public import VerifiedGarbage.Impl.P256.VerifyTable
import VerifiedGarbage.Proof.P256.VerifyTable.Store
import VerifiedGarbage.Proof.Weierstrass.AArch64.WinSelect
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-! A co-Z table entry's stores in the field invariant: entry `m`'s point and
cache slots take the values of `E` and the powers of its `Z`. -/

@[expose] public section

namespace VG.Proof.P256.VerifyTable
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

/-- Entry `m`'s five slots: its point's coordinates, then its `Z²` and `Z³`. -/
def dst (m j : Nat) : Nat := if j<3 then 2848+96*(m-1)+32*j else 6000+64*(m-1)+32*(j-3)
/-- What they are copied from: `E` and the powers of its `Z`. -/
def src (j : Nat) : Nat := if j<3 then 704+32*j else 5400+32*(j-3)
def dsts (m : Nat) : List Nat := (List.range 5).map (dst m)

/-- The field values after entry `m`'s stores. -/
def storeEnv {F : Type _} (m : Nat) (E : Nat → F) (x : Nat) : F :=
  if x=dst m 0 then E (src 0) else if x=dst m 1 then E (src 1) else
  if x=dst m 2 then E (src 2) else if x=dst m 3 then E (src 3) else
  if x=dst m 4 then E (src 4) else E x

theorem dst_inj {m : Nat} {i j : Nat} (hi : i<5) (hj : j<5) :
    dst m i=dst m j ↔ i=j :=
  ⟨fun h => by unfold dst at h; split at h <;> split at h <;> omega,fun h => h ▸ rfl⟩

theorem storeEnv_dst {F : Type _} {m : Nat} (E : Nat → F) {j : Nat} (hj : j<5) :
    storeEnv m E (dst m j)=E (src j) := by
  unfold storeEnv
  have : j=0∨j=1∨j=2∨j=3∨j=4 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl <;>
    simp (disch := decide) only [dst_inj,Nat.reduceEqDiff,↓reduceIte]

theorem storeEnv_other {F : Type _} {m : Nat} (E : Nat → F) {x : Nat} (hx : x∉dsts m) :
    storeEnv m E x=E x := by
  simp only [dsts,List.mem_map,List.mem_range,not_exists,not_and] at hx
  have h0 : x≠dst m 0 := fun h => hx 0 (by decide) h.symm
  have h1 : x≠dst m 1 := fun h => hx 1 (by decide) h.symm
  have h2 : x≠dst m 2 := fun h => hx 2 (by decide) h.symm
  have h3 : x≠dst m 3 := fun h => hx 3 (by decide) h.symm
  have h4 : x≠dst m 4 := fun h => hx 4 (by decide) h.symm
  simp only [storeEnv,h0,h1,h2,h3,h4,↓reduceIte]

theorem storeEntry_inv {Sl : Nat → Prop} (layout : Lay M 8192 Sl)
    {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State} {m : Nat}
    (hi : Inv M base 8192 C.p Sl V E s) (hm : 1≤m) (hm9 : m≤9)
    (h19 : s.gpr .x19=BitVec.ofNat 64 m)
    (hsrc : ∀ j<5,src j∈V) (hdst : ∀ j<5,Sl (dst m j)) :
    WP isa (.block VG.Impl.P256.VerifyTable.storeEntry) s fun t =>
      KeepRegs [.x1,.x2,.x16] s t ∧
      Unch base [(2848+96*(m-1),96),(6000+64*(m-1),64)] s.mem t.mem ∧
      Inv M base 8192 C.p Sl (dsts m++V) (storeEnv m E) t := by
  have hn := hi.scr.nowrap
  refine WP.mono (storeEntry_ok hi.scr hm hm9 h19) fun t ⟨we,wc,kt,ut⟩ => ⟨kt,ut,?_⟩
  have hsd (j : Nat) (hj : j<5) :
      wordsVal t.mem base (dst m j) 4=wordsVal s.mem base (src j) 4 := by
    apply wordsVal_of_words
    intro k hk
    by_cases h3 : j<3
    · have := we (4*j+k) (by omega)
      simp only [dst,src,h3,ite_true]
      rw [show 2848+96*(m-1)+32*j+8*k=2848+96*(m-1)+8*(4*j+k) by omega,
        show 704+32*j+8*k=704+8*(4*j+k) by omega]
      exact this
    · have := wc (4*(j-3)+k) (by omega)
      simp only [dst,src,h3,ite_false]
      rw [show 6000+64*(m-1)+32*(j-3)+8*k=6000+64*(m-1)+8*(4*(j-3)+k) by omega,
        show 5400+32*(j-3)+8*k=5400+8*(4*(j-3)+k) by omega]
      exact this
  have hkeep (x : Nat) (hx : x∈V) (hnd : x∉dsts m) :
      wordsVal t.mem base x 4=wordsVal s.mem base x 4 := by
    simp only [dsts,List.mem_map,List.mem_range,not_exists,not_and] at hnd
    have ap (j : Nat) (hj : j<5) := layout.apart x (dst m j) (hi.sl x hx) (hdst j hj)
      (fun h => hnd j hj h.symm)
    have a0 := ap 0 (by decide); have a1 := ap 1 (by decide); have a2 := ap 2 (by decide)
    have a3 := ap 3 (by decide); have a4 := ap 4 (by decide)
    simp only [dst,show M.n=4 from rfl,Nat.reduceLT,ite_true,ite_false] at a0 a1 a2 a3 a4
    have hb := layout.le x (hi.sl x hx)
    change x+32≤8192 at hb
    refine ut.wordsVal (fun w hw => ?_) (by omega)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl <;> dsimp only <;> omega
  refine ⟨hi.scr.of_keepRegs kt (by decide),hi.mod.unch ut (by
      intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl <;> (change 64+32≤_ ∨ _; omega)) hn,?_,?_,?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · simp only [dsts,List.mem_map,List.mem_range] at hx
      obtain ⟨j,hj,rfl⟩ := hx
      exact hdst j hj
    · exact hi.sl x hx
  · intro x hx
    by_cases hd : x∈dsts m
    · simp only [dsts,List.mem_map,List.mem_range] at hd
      obtain ⟨j,hj,rfl⟩ := hd
      change wordsVal t.mem base (dst m j) 4<_
      rw [hsd j hj]; exact hi.lt _ (hsrc j hj)
    · have hv := (List.mem_append.mp hx).resolve_left hd
      change wordsVal t.mem base x 4<_
      rw [hkeep x hv hd]; exact hi.lt x hv
  · intro x hx
    by_cases hd : x∈dsts m
    · simp only [dsts,List.mem_map,List.mem_range] at hd
      obtain ⟨j,hj,rfl⟩ := hd
      change toM _ _ (wordsVal t.mem base (dst m j) 4)=_
      rw [hsd j hj,storeEnv_dst E hj]; exact hi.val _ (hsrc j hj)
    · have hv := (List.mem_append.mp hx).resolve_left hd
      change toM _ _ (wordsVal t.mem base x 4)=_
      rw [hkeep x hv hd,storeEnv_other E hd]; exact hi.val x hv

end VG.Proof.P256.VerifyTable
