import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
import VerifiedGarbage.Impl.Weierstrass.AArch64.CachedJac
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowInvariant
import VerifiedGarbage.Proof.Weierstrass.FastNaf

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- Sixteen field elements: Z² and Z³ for each of the eight odd peer multiples. -/
def jointCacheSlots : List Nat := (List.range 16).map fun i => 6000+32*i

def jointSlots (c : Joint.Cfg) : List Nat :=
  jacWinSlots c.K ++ [5400,5432] ++ jointCacheSlots

def jointLive (c : Joint.Cfg) : List Nat := nafLive c.K ++ jointCacheSlots

def jointWork (c : Joint.Cfg) : List Nat := winOther c.K ++ [5400,5432]

def jointStableFields (c : Joint.Cfg) : List Nat :=
  [c.K.zero,c.onep] ++ jacTreeSlots c.K 9 ++ jointCacheSlots

def jointStableRanges (c : Joint.Cfg) : List (Nat × Nat) :=
  (jointStableFields c).map (·,8*c.K.M.n) ++ [(c.K.bits,257),(c.gBits,257)]

structure JointStable (c : Joint.Cfg) (C : Curve) (base : Addr)
    (Q : Point C) (u v : Nat) (s : State) : Prop where
  peer : NafStable c.K C base Q (FastNaf.byte 5 v) s
  generator : ∀ j<257,s.mem (off base (c.gBits+j))=FastNaf.byte 7 u j
  one : tmv C c.K.M.n base s c.onep=1
  cache2 : ∀ i<8,tmv C c.K.M.n base s (VG.Impl.Weierstrass.CachedJac.tableZ2 i)=
    tmv C c.K.M.n base s (Jacobian.tablePt c.K (i+1)).z *
    tmv C c.K.M.n base s (Jacobian.tablePt c.K (i+1)).z
  cache3 : ∀ i<8,tmv C c.K.M.n base s (VG.Impl.Weierstrass.CachedJac.tableZ3 i)=
    tmv C c.K.M.n base s (VG.Impl.Weierstrass.CachedJac.tableZ2 i) *
    tmv C c.K.M.n base s (Jacobian.tablePt c.K (i+1)).z

/-- The external read-only generator row can be supplied by the verifier's own invariant. -/
structure JointCore (c : Joint.Cfg) (C : Curve) (base : Addr) (size : Nat)
    (Q : Point C) (u v : Nat) (External : State → Prop) (A : Point C) (s : State) : Prop where
  field : Inv c.K.M base size C.p (·∈jointSlots c) (jointLive c) (tmv C c.K.M.n base s) s
  stable : JointStable c C base Q u v s
  external : External s
  point : InvJ C (tmv C c.K.M.n base s c.K.R.x) (tmv C c.K.M.n base s c.K.R.y)
    (tmv C c.K.M.n base s c.K.R.z) A

theorem jointStable_table (c : Joint.Cfg) {a : Nat} (ha : 1≤a) (hb : a≤9)
    {x : Nat} (hx : x∈[(Jacobian.tablePt c.K a).x,(Jacobian.tablePt c.K a).y,(Jacobian.tablePt c.K a).z]) :
    x∈jointStableFields c := by
  apply List.mem_append_left
  apply List.mem_append_right
  simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact List.mem_map.mpr ⟨3*(a-1),List.mem_range.mpr (by omega),by omega⟩
  · exact List.mem_map.mpr ⟨3*(a-1)+1,List.mem_range.mpr (by omega),by omega⟩
  · exact List.mem_map.mpr ⟨3*(a-1)+2,List.mem_range.mpr (by omega),by omega⟩

theorem jointStable_cache2 (c : Joint.Cfg) {i : Nat} (hi : i<8) :
    VG.Impl.Weierstrass.CachedJac.tableZ2 i∈jointStableFields c := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨2*i,List.mem_range.mpr (by omega),by
    simp only [VG.Impl.Weierstrass.CachedJac.tableZ2]; omega⟩

theorem jointStable_cache3 (c : Joint.Cfg) {i : Nat} (hi : i<8) :
    VG.Impl.Weierstrass.CachedJac.tableZ3 i∈jointStableFields c := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨2*i+1,List.mem_range.mpr (by omega),by
    simp only [VG.Impl.Weierstrass.CachedJac.tableZ3]; omega⟩

theorem JointStable.keep {c : Joint.Cfg} {C : Curve} {base : Addr} {Q : Point C} {u v : Nat}
    {s t : State} {W : List Nat} (h : JointStable c C base Q u v s)
    (hk : ProgKeep c.K.M base W s t)
    (hb : ∀ r∈jointStableRanges c,r.1+r.2≤2^64)
    (hsep : ∀ r∈jointStableRanges c,∀ w∈W.map (·,8*c.K.M.n)++[(c.K.M.tmp,8*c.K.M.n)],
      r.1+r.2≤w.1 ∨ w.1+w.2≤r.1) : JointStable c C base Q u v t := by
  have hrange (x : Nat) (hx : x∈jointStableFields c) : (x,8*c.K.M.n)∈jointStableRanges c :=
    List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
  have hw (x : Nat) (hx : x∈jointStableFields c) :
      wordsVal t.mem base x c.K.M.n=wordsVal s.mem base x c.K.M.n :=
    hk.unch.wordsVal (hsep _ (hrange x hx)) (hb _ (hrange x hx))
  have hf (x : Nat) (hx : x∈jointStableFields c) :
      tmv C c.K.M.n base t x=tmv C c.K.M.n base s x := by
    unfold tmv; rw [hw x hx]
  have hbits (d : Nat) (ho : (d,257)∈jointStableRanges c) (j : Nat) (hj : j<257) :
      t.mem (off base (d+j))=s.mem (off base (d+j)) := by
    apply hk.unch.byte
    · intro w hw
      have := hsep _ ho w hw
      dsimp only at this ⊢; omega
    · have := hb _ ho; dsimp only at this; omega
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_,?_⟩
  · rw [hw c.K.zero (by simp [jointStableFields]),h.peer.zero]
  · intro a ha hb
    rw [hf _ (jointStable_table c ha (by omega) (by simp)),
      hf _ (jointStable_table c ha (by omega) (by simp)),
      hf _ (jointStable_table c ha (by omega) (by simp))]
    exact h.peer.table a ha hb
  · intro j hj
    rw [hbits c.K.bits (by simp [jointStableRanges]) j hj]
    exact h.peer.bits j hj
  · intro j hj
    rw [hbits c.gBits (by simp [jointStableRanges]) j hj]
    exact h.generator j hj
  · rw [hf c.onep (by simp [jointStableFields]),h.one]
  · intro i hi
    rw [hf _ (jointStable_cache2 c hi),hf _ (jointStable_table c (a:=i+1) (by omega) (by omega) (by simp))]
    exact h.cache2 i hi
  · intro i hi
    rw [hf _ (jointStable_cache3 c hi),hf _ (jointStable_cache2 c hi),
      hf _ (jointStable_table c (a:=i+1) (by omega) (by omega) (by simp))]
    exact h.cache3 i hi

theorem JointStable.of_mem {c : Joint.Cfg} {C : Curve} {base : Addr} {Q : Point C} {u v : Nat}
    {s t : State} (h : JointStable c C base Q u v s) (hm : t.mem=s.mem) :
    JointStable c C base Q u v t := by
  have he : tmv C c.K.M.n base t=tmv C c.K.M.n base s := by
    funext x; unfold tmv; rw [hm]
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_,?_⟩
  · rw [hm]; exact h.peer.zero
  · intro a ha hb; rw [he]; exact h.peer.table a ha hb
  · intro j hj; rw [hm]; exact h.peer.bits j hj
  · intro j hj; rw [hm]; exact h.generator j hj
  · rw [he]; exact h.one
  · intro i hi; rw [he]; exact h.cache2 i hi
  · intro i hi; rw [he]; exact h.cache3 i hi

theorem JointCore.of_keeps {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v : Nat}
    {Q A : Point C} {External : State → Prop} {s t : State} {rs : List Reg}
    (h : JointCore c C base size Q u v External A s)
    (hk : VG.Proof.Ed25519.AArch64.Keeps rs s t) (h0 : Reg.x0∉rs) (ht : External t) :
    JointCore c C base size Q u v External A t := by
  have he : tmv C c.K.M.n base t=tmv C c.K.M.n base s := by
    funext x; unfold tmv; rw [hk.mem]
  refine ⟨?_,h.stable.of_mem hk.mem,ht,?_⟩
  · rw [he]; exact h.field.of_keeps hk h0
  · rw [he]; exact h.point

structure JointLayout (c : Joint.Cfg) (size : Nat) : Prop where
  lay : Lay c.K.M size (·∈jointSlots c)
  aligned : Aligned c.K.M (·∈jointSlots c)
  n : c.K.M.n=4
  stableBounds : ∀ r∈jointStableRanges c,r.1+r.2≤size
  stableSep : ∀ r∈jointStableRanges c,∀ w∈(jointWork c).map (·,8*c.K.M.n)++[(c.K.M.tmp,8*c.K.M.n)],
    r.1+r.2≤w.1 ∨ w.1+w.2≤r.1

theorem jointLive_R (c : Joint.Cfg) : ∀ x∈[c.K.R.x,c.K.R.y,c.K.R.z],x∈jointLive c :=
  fun x hx => List.mem_append_left _ (nafLive_R c.K x hx)

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
    (hn : ∀ x∈[c.K.R.x,c.K.R.y,c.K.R.z],x∉W)
    (hi : Inv c.K.M base size C.p (·∈jointSlots c) (jointLive c) E t) (ht : External t) :
    JointCore c C base size Q u v External A t := by
  have same (x : Nat) (hx : x∈[c.K.R.x,c.K.R.y,c.K.R.z]) :
      tmv C c.K.M.n base t x=tmv C c.K.M.n base s x := by
    have hxs := h.field.sl x (jointLive_R c x hx)
    unfold tmv
    rw [hk.unch.wordsVal (fun w hw' => ?_) (by
      have := hL.lay.le x hxs; have := h.field.scr.nowrap; omega)]
    simp only [List.mem_append,List.mem_map,List.mem_singleton] at hw'
    rcases hw' with ⟨y,hy,rfl⟩ | rfl
    · exact hL.lay.apart x y hxs (hsl y hy) (fun he => hn x hx (he ▸ hy))
    · exact hL.lay.tmp x hxs
  refine ⟨hi.to_tmv,h.stable.keep (hk.mono hw) (fun r hr => by
    have := hL.stableBounds r hr; have := h.field.scr.nowrap; omega) hL.stableSep,ht,?_⟩
  rw [same _ (by simp),same _ (by simp),same _ (by simp)]
  exact h.point

end VG.Proof.Weierstrass.AArch64
