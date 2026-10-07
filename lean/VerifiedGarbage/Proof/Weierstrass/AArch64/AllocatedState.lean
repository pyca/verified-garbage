import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointGenerator

/-! Transfer only initialized field values and stable data across allocated
arithmetic. Dead intermediate words and temporary registers need not agree. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

/-- Observations are needed only for words of valid field slots. The actual
scratch and modulus invariants come from the candidate's own memory frame. -/
theorem Inv.of_observed {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {s t : State}
    (h : Inv M base size m Sl V E s) (hs : Scr t base size)
    (hm : ModOkA M size m t.mem base)
    (hw : ∀ x∈V,∀ i<M.n,word t.mem base (x+8*i)=word s.mem base (x+8*i)) :
    Inv M base size m Sl V E t := by
  have hv (x : Nat) (hx : x∈V) : wordsVal t.mem base x M.n=wordsVal s.mem base x M.n :=
    by apply wordsVal_of_words₂; exact hw x hx
  exact ⟨hs,hm,h.sl,fun x hx => by rw [hv x hx]; exact h.lt x hx,
    fun x hx => by rw [hv x hx]; exact h.val x hx⟩

theorem JointStable.allocatedKeep {c : Joint.Cfg} {C : Curve} {base : Addr} {Q : Point C} {u v : Nat}
    {s t : State} {W : List (Nat × Nat)} (h : JointStable c C base Q u v s)
    (hk : Unch base W s.mem t.mem)
    (hb : ∀ r∈jointStableRanges c,r.1+r.2≤2^64)
    (hsep : ∀ r∈jointStableRanges c,∀ w∈W,
      r.1+r.2≤w.1 ∨ w.1+w.2≤r.1) : JointStable c C base Q u v t := by
  have hrange (x : Nat) (hx : x∈jointStableFields c) : (x,8*c.K.M.n)∈jointStableRanges c :=
    List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
  have hw (x : Nat) (hx : x∈jointStableFields c) :
      wordsVal t.mem base x c.K.M.n=wordsVal s.mem base x c.K.M.n :=
    hk.wordsVal (hsep _ (hrange x hx)) (hb _ (hrange x hx))
  have hf (x : Nat) (hx : x∈jointStableFields c) :
      tmv C c.K.M.n base t x=tmv C c.K.M.n base s x := by
    unfold tmv; rw [hw x hx]
  have hbits (d : Nat) (ho : (d,257)∈jointStableRanges c) (j : Nat) (hj : j<257) :
      t.mem (off base (d+j))=s.mem (off base (d+j)) := by
    apply hk.byte
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

theorem JointGenerator.allocatedKeep {c : Joint.Cfg} {C : Curve} {base T : Addr} {size : Nat}
    {G : Point C} {s t : State} {rs : List Reg} {W : List (Nat × Nat)} (h : JointGenerator c C base size G T s)
    (hk : AllocatedFrame rs base W s t) (hsym : t.syms=s.syms)
    (hw : ∀ w∈W,w.1+w.2≤size) :
    JointGenerator c C base size G T t := by
  have wordeq (a i : Nat) (ha : 1≤a) (ha32 : a≤32) (hi : i<8) :
      word t.mem (T+BitVec.ofNat 64 (128*(a-1))) (8*i)=
      word s.mem (T+BitVec.ofNat 64 (128*(a-1))) (8*i) := by
    apply Mem.readW_congr
    intro b hb
    have ho := h.outside a ha ha32 i hi b (by omega)
    apply hk.unch
    intro w hm
    have := hw w hm
    dsimp only [off]; exact Or.inr (by omega)
  have val (a o : Nat) (ha : 1≤a) (ha32 : a≤32) (ho : o=0 ∨ o=32) :
      wordsVal t.mem (T+BitVec.ofNat 64 (128*(a-1))) o 4=
      wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) o 4 := by
    apply wordsVal_of_words₂
    intro i hi
    rcases ho with rfl | rfl
    · simpa only [Nat.zero_add] using wordeq a i ha ha32 (by omega)
    · have e := wordeq a (4+i) ha ha32 (by omega)
      simpa only [Nat.mul_add] using e
  refine ⟨?_,?_,h.outside,?_,?_⟩
  · rw [hsym]; exact h.symbol
  · intro a ha ha32 i hi; rw [hk.regs.rd,hk.regs.wr]; exact h.read a ha ha32 i hi
  · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 32 ha ha32 (by simp)]
    exact h.bounds a ha ha32
  · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 32 ha ha32 (by simp)]
    exact h.point a ha ha32

/-- The mathematical accumulator advances while stable tables and digits are
framed independently of the arithmetic's internal register allocation. -/
theorem JointCore.allocatedNext {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v : Nat}
    {Q A B : Point C} {External : State → Prop} {s t : State} {E : Nat → Fe C}
    {rs : List Reg} {W : List (Nat × Nat)}
    (h : JointCore c C base size Q u v External A s) (hL : JointLayout c size)
    (hk : AllocatedFrame rs base W s t)
    (hsep : ∀ r∈jointStableRanges c,∀ w∈W,r.1+r.2≤w.1 ∨ w.1+w.2≤r.1)
    (hi : Inv c.K.M base size C.p (·∈jointSlots c) (jointLive c) E t)
    (hp : InvJ C (E c.K.R.x) (E c.K.R.y) (E c.K.R.z) B) (ht : External t) :
    JointCore c C base size Q u v External B t :=
  ⟨hi.to_tmv,h.stable.allocatedKeep hk.unch (fun r hr => by
    have := hL.stableBounds r hr; have := h.field.scr.nowrap; omega) hsep,
    ht,hi.point_tmv (jointLive_R c) hp⟩

end VG.Proof.Weierstrass.AArch64
