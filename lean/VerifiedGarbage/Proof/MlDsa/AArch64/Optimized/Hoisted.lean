import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Registers
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Table

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def outerRegs : List VReg := [.v18,.v19] ++ groupRegs

/-- The four loaded vectors hold eight interleaved roots and exact reciprocals. -/
structure Hoisted (s : State) (z : Nat → Int) : Prop where
  range : ∀ i < 8, 0 ≤ z (i+1) ∧ z (i+1) < 8380417
  q : ∀ e < 4, vword (s.v .v16) e = 8380417#32
  roots : ∀ g < 4, ∀ e < 4, vword (s.v rootRegs[g]!) e =
    if e % 2 = 0 then BitVec.ofInt 32 (z (2*g+e/2+1))
    else BitVec.ofInt 32 (reciprocal (z (2*g+e/2+1)))

theorem Hoisted.keep {s t : State} {z : Nat → Int} (h : Hoisted s z)
    (hc : VChg outerRegs s t) : Hoisted t z := by
  refine ⟨h.range, ?_, ?_⟩
  · intro e he
    rw [hc.get .v16 (by decide)]
    exact h.q e he
  · intro g hg e he
    have hn : ∀ i : Fin 4, rootRegs[i.val]! ∉ outerRegs := by decide
    rw [hc.get _ (hn ⟨g,hg⟩)]
    exact h.roots g hg e he

theorem GoodRen.root_keep {r : Ren} {s t : State} {values : Vector (BitVec 128) 8}
    (hr : GoodRen r) (h : Bank s r.data values) (hc : VChg [.v18,.v19] s t) :
    Bank t r.data values := by
  intro i
  have hn : ∀ v ∈ liveRegs, v ∉ [VReg.v18,.v19] := by decide
  rw [hc.get _ (hn _ (hr.data i))]
  exact h i

/-- Extract a chosen outer-layer root without modifying the hoisted constants. -/
theorem hoistedRoot_ok (index : Nat) (hi : 1 ≤ index) (hi' : index ≤ 8)
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (h : Hoisted s z)
    (k : ∀ t, VChg [.v18,.v19] s t →
      (∀ e < 4, vword (t.v .v18) e = BitVec.ofInt 32 (z index)) →
      (∀ e < 4, vword (t.v .v19) e = BitVec.ofInt 32 (reciprocal (z index))) →
      WP isa (.block rest) t Q) :
    WP isa (.block (hoistedRoot index ++ rest)) s Q := by
  have hg : (index-1)/2 < 4 := by omega
  have hp : (index-1)%2 < 2 := by omega
  have hs : ∀ g : Fin 4, rootRegs[g.val]! ≠ .v18 := by decide
  refine rootPair_ok rootRegs[(index-1)/2]! ((index-1)%2) hp (hs ⟨_,hg⟩) fun t hc ha hb => ?_
  refine k t hc ?_ ?_
  · intro e he
    rw [ha e he, h.roots _ hg _ (by omega)]
    have hm : (2*((index-1)%2))%2 = 0 := by omega
    have heq : 2*((index-1)/2)+(2*((index-1)%2))/2+1 = index := by omega
    rw [hm, ite_eq_left rfl, heq]
  · intro e he
    rw [hb e he, h.roots _ hg _ (by omega)]
    have hm : ¬ (2*((index-1)%2)+1)%2 = 0 := by omega
    have heq : 2*((index-1)/2)+(2*((index-1)%2)+1)/2+1 = index := by omega
    rw [ite_eq_right hm, heq]

end VG.Proof.MlDsa.AArch64.Optimized
