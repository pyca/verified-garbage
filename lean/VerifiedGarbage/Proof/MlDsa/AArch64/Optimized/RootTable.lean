import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveSlice
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.SliceFrame
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64

def innerOffset (gap : Nat) : Nat := if gap=4 then 0 else if gap=2 then 32 else 96

def tailOffset (len : Nat) : Nat := if len=2 then 224 else 352

def rootAddress (p : Addr) (u offset g b : Nat) : Addr :=
  p+BitVec.ofNat 64 (480*u+offset+32*g+b)

def expandedRegion (p : Addr) : Region := ⟨p,3904⟩

theorem inner_contains (p : Addr) {u gap g b : Nat} (hu : u<8) (hg : ValidGroup gap g)
    (hb : b=0 ∨ b=16) : (expandedRegion p).Contains (rootAddress p u (innerOffset gap) g b) 16 := by
  have h : 480*u+innerOffset gap+32*g+b+16 ≤ 3904 := by
    rcases hg with ⟨rfl,rfl⟩ | ⟨rfl,hg⟩ | ⟨rfl,hg⟩ <;>
      simp only [innerOffset,ite_true,show ¬2=4 by decide,show ¬1=4 by decide,show ¬1=2 by decide,ite_false] <;> omega
  exact Offset.contains_base p h (by omega)

theorem tail_contains (p : Addr) {u len g b : Nat} (hu : u<8) (hg : g<4)
    (hl : len=1 ∨ len=2) (hb : b=0 ∨ b=16) :
    (expandedRegion p).Contains (rootAddress p u (tailOffset len) g b) 16 := by
  have h : 480*u+tailOffset len+32*g+b+16 ≤ 3904 := by
    rcases hl with rfl | rfl <;> simp only [tailOffset,show ¬1=2 by decide,ite_false,ite_true] <;> omega
  exact Offset.contains_base p h (by omega)

/-- Logical values of the immutable prearranged inner table, independent of
its assembler symbol or host allocation. -/
structure RootTable (m : Mem) (p : Addr) (zi zt : Nat → Nat → Nat → Nat → Int) : Prop where
  inner_range : ∀ u < 8, ∀ gap g, ValidGroup gap g → ∀ e < 4,
    0 ≤ zi u gap g e ∧ zi u gap g e < 8380417
  tail_range : ∀ u < 8, ∀ g < 4, ∀ len, len=1 ∨ len=2 → ∀ e < 4,
    0 ≤ zt u g len e ∧ zt u g len e < 8380417
  inner_root : ∀ u < 8, ∀ gap g, ValidGroup gap g → ∀ e < 4,
    vword (m.read (rootAddress p u (innerOffset gap) g 0) 16) e = BitVec.ofInt 32 (zi u gap g e)
  inner_reciprocal : ∀ u < 8, ∀ gap g, ValidGroup gap g → ∀ e < 4,
    vword (m.read (rootAddress p u (innerOffset gap) g 16) 16) e =
      BitVec.ofInt 32 (reciprocal (zi u gap g e))
  tail_root : ∀ u < 8, ∀ g < 4, ∀ len, len=1 ∨ len=2 → ∀ e < 4,
    vword (m.read (rootAddress p u (tailOffset len) g 0) 16) e = BitVec.ofInt 32 (zt u g len e)
  tail_reciprocal : ∀ u < 8, ∀ g < 4, ∀ len, len=1 ∨ len=2 → ∀ e < 4,
    vword (m.read (rootAddress p u (tailOffset len) g 16) 16) e =
      BitVec.ofInt 32 (reciprocal (zt u g len e))

theorem RootTable.frame {m m' : Mem} {p : Addr} {zi zt : Nat → Nat → Nat → Nat → Int}
    {W : List Region} (h : RootTable m p zi zt) (hf : Frame W m m')
    (hd : ∀ r ∈ W, (expandedRegion p).Disjoint r) : RootTable m' p zi zt := by
  refine ⟨h.inner_range,h.tail_range,?_,?_,?_,?_⟩
  · intro u hu gap g hg e he
    rw [hf.read (inner_contains p hu hg (Or.inl rfl)) hd (by decide)]
    exact h.inner_root u hu gap g hg e he
  · intro u hu gap g hg e he
    rw [hf.read (inner_contains p hu hg (Or.inr rfl)) hd (by decide)]
    exact h.inner_reciprocal u hu gap g hg e he
  · intro u hu g hg len hl e he
    rw [hf.read (tail_contains p hu hg hl (Or.inl rfl)) hd (by decide)]
    exact h.tail_root u hu g hg len hl e he
  · intro u hu g hg len hl e he
    rw [hf.read (tail_contains p hu hg hl (Or.inr rfl)) hd (by decide)]
    exact h.tail_reciprocal u hu g hg len hl e he

structure FivePointers (s : State) (p : Addr) (u : Nat) : Prop where
  inner : ∀ gap, s.gpr (innerBase gap) = p+BitVec.ofNat 64 (480*u+innerOffset gap)
  tail : ∀ len, s.gpr (tailBase len) = p+BitVec.ofNat 64 (480*u+tailOffset len)

theorem FivePointers.inner_addr {s : State} {p : Addr} {u : Nat} (h : FivePointers s p u)
    (gap g b : Nat) : s.gpr (innerBase gap)+BitVec.ofNat 64 (32*g+b) =
      rootAddress p u (innerOffset gap) g b := by
  simp only [h.inner,rootAddress,BitVec.ofNat_add,BitVec.add_assoc]

theorem FivePointers.tail_addr {s : State} {p : Addr} {u : Nat} (h : FivePointers s p u)
    (len g b : Nat) : s.gpr (tailBase len)+BitVec.ofNat 64 (32*g+b) =
      rootAddress p u (tailOffset len) g b := by
  simp only [h.tail,rootAddress,BitVec.ofNat_add,BitVec.add_assoc]

theorem RootTable.roots {s : State} {p : Addr} {u : Nat} {zi zt : Nat → Nat → Nat → Nat → Int}
    (h : RootTable s.mem p zi zt) (hu : u<8) (hp : FivePointers s p u)
    (hr : expandedRegion p ∈ s.rd++s.wr) (hq : ∀ e < 4, vword (s.v .v16) e = 8380417#32) :
    InnerRoots s (zi u) ∧ TailRoots s (zt u) := by
  constructor
  · refine ⟨h.inner_range u hu,hq,?_,?_,?_⟩
    · intro gap g hg b hb
      rw [hp.inner_addr]
      exact ⟨_,hr,inner_contains p hu hg (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hb)⟩
    · intro gap g hg e he
      have ha := hp.inner_addr gap g 0
      simp only [Nat.add_zero] at ha
      rw [ha]
      exact h.inner_root u hu gap g hg e he
    · intro gap g hg e he
      rw [hp.inner_addr]
      exact h.inner_reciprocal u hu gap g hg e he
  · refine ⟨hq,h.tail_range u hu,?_,?_,?_⟩
    · intro g hg len hl b hb
      rw [hp.tail_addr]
      exact ⟨_,hr,tail_contains p hu hg hl (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hb)⟩
    · intro g hg len hl e he
      have ha := hp.tail_addr len g 0
      simp only [Nat.add_zero] at ha
      rw [ha]
      exact h.tail_root u hu g hg len hl e he
    · intro g hg len hl e he
      rw [hp.tail_addr]
      exact h.tail_reciprocal u hu g hg len hl e he

end VG.Proof.MlDsa.AArch64.Optimized
