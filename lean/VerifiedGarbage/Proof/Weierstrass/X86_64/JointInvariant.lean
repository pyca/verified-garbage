import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafLayout
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
import VerifiedGarbage.Proof.Weierstrass.FastNaf
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafArith

/-! Stable tables and public digits around the shared Jacobian accumulator. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

def jointCacheSlots (c : Joint.Cfg) : List Nat := (List.range 16).map fun i => c.cache+8*c.K.M.n*i

def jointSlots (c : Joint.Cfg) : List Nat :=
  nafSlots c.K++[c.selected,c.selected+8*c.K.M.n]++jointCacheSlots c

def jointLive (c : Joint.Cfg) : List Nat := winRo c.K++jacCoords c.K.R++nafTblSlots c.K++jointCacheSlots c

def jointWork (c : Joint.Cfg) : List Nat := winOther c.K++[c.selected,c.selected+8*c.K.M.n]

def jointStableFields (c : Joint.Cfg) : List Nat := winRo c.K++nafTblSlots c.K++jointCacheSlots c

def jointStableRanges (c : Joint.Cfg) : List (Nat×Nat) :=
  (jointStableFields c).map (·,8*c.K.M.n)++[(c.K.bits,64*c.K.M.n+1),(c.gBits,64*c.K.M.n+1)]

structure JointStable (c : Joint.Cfg) (C : Curve) (base : Addr)
    (Q : Point C) (u v : Nat) (s : State) : Prop where
  zero : tmv C c.K.M.n base s c.K.zero=0
  table : ∀ a,1≤a → a≤8 → InvJ C (tmv C c.K.M.n base s (c.K.tblPt a).x)
    (tmv C c.K.M.n base s (c.K.tblPt a).y) (tmv C c.K.M.n base s (c.K.tblPt a).z) (mul (2*a-1) Q)
  peer : ∀ j<64*c.K.M.n+1,s.mem (off base (c.K.bits+j))=FastNaf.byte 5 v j
  generator : ∀ j<64*c.K.M.n+1,s.mem (off base (c.gBits+j))=FastNaf.byte 7 u j
  cache2 : ∀ i<8,tmv C c.K.M.n base s (c.cache+16*c.K.M.n*i)=
    tmv C c.K.M.n base s (c.K.tblPt (i+1)).z*tmv C c.K.M.n base s (c.K.tblPt (i+1)).z
  cache3 : ∀ i<8,tmv C c.K.M.n base s (c.cache+16*c.K.M.n*i+8*c.K.M.n)=
    tmv C c.K.M.n base s (c.cache+16*c.K.M.n*i)*tmv C c.K.M.n base s (c.K.tblPt (i+1)).z

structure JointCore (c : Joint.Cfg) (C : Curve) (base : Addr) (size : Nat)
    (Q : Point C) (u v : Nat) (External : State → Prop) (A : Point C) (s : State) : Prop where
  field : Inv c.K.M base size C.p (·∈jointSlots c) (jointLive c) (tmv C c.K.M.n base s) s
  stable : JointStable c C base Q u v s
  external : External s
  point : InvJ C (tmv C c.K.M.n base s c.K.R.x) (tmv C c.K.M.n base s c.K.R.y)
    (tmv C c.K.M.n base s c.K.R.z) A

theorem jointStable_table (c : Joint.Cfg) {a : Nat} (ha : 1≤a) (hb : a≤9)
    {x : Nat} (hx : x∈jacCoords (c.K.tblPt a)) : x∈jointStableFields c := by
  apply List.mem_append_left
  apply List.mem_append_right
  simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl
  · rw [tblPt_x]; exact nafTbl_slot c.K (by omega)
  · rw [tblPt_y]; exact nafTbl_slot c.K (by omega)
  · rw [tblPt_z]; exact nafTbl_slot c.K (by omega)

theorem jointStable_cache2 (c : Joint.Cfg) {i : Nat} (hi : i<8) :
    c.cache+16*c.K.M.n*i∈jointStableFields c :=
  List.mem_append_right _ (List.mem_map.mpr ⟨2*i,List.mem_range.mpr (by omega),
    by rw [slot_two_mul]⟩)

theorem jointStable_cache3 (c : Joint.Cfg) {i : Nat} (hi : i<8) :
    c.cache+16*c.K.M.n*i+8*c.K.M.n∈jointStableFields c :=
  List.mem_append_right _ (List.mem_map.mpr ⟨2*i+1,List.mem_range.mpr (by omega),
    by rw [slot_two_mul_add,Nat.add_assoc]⟩)

theorem JointStable.keep {c : Joint.Cfg} {C : Curve} {base : Addr} {Q : Point C} {u v : Nat}
    {s t : State} {W : List Nat} (h : JointStable c C base Q u v s)
    (hk : ProgKeep c.K.M base W s t)
    (hb : ∀ r∈jointStableRanges c,r.1+r.2≤2^64)
    (hsep : ∀ r∈jointStableRanges c,∀ w∈W.map (·,8*c.K.M.n)++[(c.K.M.tmp,8*c.K.M.n)],
      r.1+r.2≤w.1 ∨ w.1+w.2≤r.1) : JointStable c C base Q u v t := by
  have hrange (x : Nat) (hx : x∈jointStableFields c) : (x,8*c.K.M.n)∈jointStableRanges c :=
    List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
  have hf (x : Nat) (hx : x∈jointStableFields c) :
      tmv C c.K.M.n base t x=tmv C c.K.M.n base s x := by
    unfold tmv
    rw [hk.unch.wordsVal (hsep _ (hrange x hx)) (hb _ (hrange x hx))]
  have hbits (d : Nat) (ho : (d,64*c.K.M.n+1)∈jointStableRanges c) (j : Nat) (hj : j<64*c.K.M.n+1) :
      t.mem (off base (d+j))=s.mem (off base (d+j)) := by
    apply hk.unch.byte
    · intro w hw
      have := hsep _ ho w hw
      dsimp only at this ⊢; omega
    · have := hb _ ho; dsimp only at this; omega
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hf c.K.zero (by simp [jointStableFields,winRo]),h.zero]
  · intro a ha hb
    rw [hf _ (jointStable_table c ha (by omega) (by simp [jacCoords])),
      hf _ (jointStable_table c ha (by omega) (by simp [jacCoords])),
      hf _ (jointStable_table c ha (by omega) (by simp [jacCoords]))]
    exact h.table a ha hb
  · intro j hj
    rw [hbits c.K.bits (by simp [jointStableRanges]) j hj]
    exact h.peer j hj
  · intro j hj
    rw [hbits c.gBits (by simp [jointStableRanges]) j hj]
    exact h.generator j hj
  · intro i hi
    rw [hf _ (jointStable_cache2 c hi),hf _ (jointStable_table c (a:=i+1) (by omega) (by omega) (by simp [jacCoords]))]
    exact h.cache2 i hi
  · intro i hi
    rw [hf _ (jointStable_cache3 c hi),hf _ (jointStable_cache2 c hi),
      hf _ (jointStable_table c (a:=i+1) (by omega) (by omega) (by simp [jacCoords]))]
    exact h.cache3 i hi

theorem JointStable.of_mem {c : Joint.Cfg} {C : Curve} {base : Addr} {Q : Point C} {u v : Nat}
    {s t : State} (h : JointStable c C base Q u v s) (hm : t.mem=s.mem) :
    JointStable c C base Q u v t := by
  have he : tmv C c.K.M.n base t=tmv C c.K.M.n base s := by
    funext x; unfold tmv; rw [hm]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [he]; exact h.zero
  · intro a ha hb; rw [he]; exact h.table a ha hb
  · intro j hj; rw [hm]; exact h.peer j hj
  · intro j hj; rw [hm]; exact h.generator j hj
  · intro i hi; rw [he]; exact h.cache2 i hi
  · intro i hi; rw [he]; exact h.cache3 i hi

theorem JointCore.of_keeps {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v : Nat}
    {Q A : Point C} {External : State → Prop} {s t : State} {rs : List Reg}
    (h : JointCore c C base size Q u v External A s)
    (hk : Keeps rs s t) (hr : Reg.rdi∉rs) (ht : External t) :
    JointCore c C base size Q u v External A t := by
  have he : tmv C c.K.M.n base t=tmv C c.K.M.n base s := by
    funext x; unfold tmv; rw [hk.2.1]
  refine ⟨?_,h.stable.of_mem hk.2.1,ht,?_⟩
  · rw [he]; exact h.field.of_keeps hk hr
  · rw [he]; exact h.point

structure JointLayout (c : Joint.Cfg) (size : Nat) : Prop where
  lay : Lay c.K.M size (·∈jointSlots c)
  n : c.K.M.n=4 ∨ c.K.M.n=6
  stableBounds : ∀ r∈jointStableRanges c,r.1+r.2≤size
  stableSep : ∀ r∈jointStableRanges c,∀ w∈(jointWork c).map (·,8*c.K.M.n)++[(c.K.M.tmp,8*c.K.M.n)],
    r.1+r.2≤w.1 ∨ w.1+w.2≤r.1

theorem jointLive_R (c : Joint.Cfg) : ∀ x∈jacCoords c.K.R,x∈jointLive c := by
  intro x hx
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx))

theorem JointCore.next {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v : Nat}
    {Q A B : Point C} {External : State → Prop} {s t : State} {E : Nat → Fe C}
    (h : JointCore c C base size Q u v External A s) (hL : JointLayout c size)
    (hk : ProgKeep c.K.M base (jointWork c) s t)
    (hi : Inv c.K.M base size C.p (·∈jointSlots c) (jointLive c) E t)
    (hp : InvJ C (E c.K.R.x) (E c.K.R.y) (E c.K.R.z) B) (ht : External t) :
    JointCore c C base size Q u v External B t :=
  ⟨hi.to_tmv,h.stable.keep hk (fun r hr => by
    have := hL.stableBounds r hr; have := h.field.scr.nowrap; omega) hL.stableSep,
    ht,hi.point_tmv (jointLive_R c) hp⟩

theorem JointCore.of_write {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v : Nat}
    {Q A : Point C} {External : State → Prop} {s t : State} {E : Nat → Fe C} {W : List Nat}
    (h : JointCore c C base size Q u v External A s) (hL : JointLayout c size)
    (hk : ProgKeep c.K.M base W s t) (hw : ∀ x∈W,x∈jointWork c)
    (hsl : ∀ x∈W,x∈jointSlots c)
    (hn : ∀ x∈jacCoords c.K.R,x∉W)
    (hi : Inv c.K.M base size C.p (·∈jointSlots c) (jointLive c) E t) (ht : External t) :
    JointCore c C base size Q u v External A t :=
  ⟨hi.to_tmv,h.stable.keep (hk.mono hw) (fun r hr => by
    have := hL.stableBounds r hr; have := h.field.scr.nowrap; omega) hL.stableSep,ht,
    hk.invJ hL.lay h.field.scr hsl (fun x hx => h.field.sl x (jointLive_R c x hx)) hn h.point⟩

end VG.Proof.Weierstrass.X86_64
