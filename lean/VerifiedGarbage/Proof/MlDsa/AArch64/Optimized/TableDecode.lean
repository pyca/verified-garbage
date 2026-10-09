import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableMemory

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem ExpandedWords.inner_values {m : Mem} {p : Addr} (h : ExpandedWords m p)
    {u gap g e : Nat} (hu : u<8) (hg : ValidGroup gap g) (he : e<4) :
    vword (m.read (rootAddress p u (innerOffset gap) g 0) 16) e=BitVec.ofInt 32 (innerRoot u gap g e) ∧
    vword (m.read (rootAddress p u (innerOffset gap) g 16) 16) e=
      BitVec.ofInt 32 (reciprocal (innerRoot u gap g e)) := by
  rcases hg with ⟨rfl,rfl⟩ | ⟨rfl,hg⟩ | ⟨rfl,hg⟩
  · exact h.row (by decide) he (by change 480*u+0+32*0+32≤3904; omega) (by
      simpa only [innerOffset,innerRoot,ite_true,Nat.zero_div,Nat.mul_zero,Nat.add_zero] using TableConstants.inner4_values hu he)
  · have hg' : g<2 := by omega
    exact h.row (by decide) he (by change 480*u+32+32*g+32≤3904; omega) (TableConstants.inner2_values hu hg' he)
  · exact h.row (by decide) he (by change 480*u+96+32*g+32≤3904; omega) (TableConstants.inner1_values hu hg he)

theorem ExpandedWords.tail_values {m : Mem} {p : Addr} (h : ExpandedWords m p)
    {u len g e : Nat} (hu : u<8) (hg : g<4) (hl : len=1 ∨ len=2) (he : e<4) :
    vword (m.read (rootAddress p u (tailOffset len) g 0) 16) e=BitVec.ofInt 32 (tailRoot u g len e) ∧
    vword (m.read (rootAddress p u (tailOffset len) g 16) 16) e=
      BitVec.ofInt 32 (reciprocal (tailRoot u g len e)) := by
  rcases hl with rfl | rfl
  · exact h.row (by decide) he (by change 480*u+352+32*g+32≤3904; omega) (TableConstants.tail1_values hu hg he)
  · exact h.row (by decide) he (by change 480*u+224+32*g+32≤3904; omega) (TableConstants.tail2_values hu hg he)

theorem ExpandedWords.roots {m : Mem} {p : Addr} (h : ExpandedWords m p) :
    RootTable m p innerRoot tailRoot := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro u _ gap g _ e _
    exact ordinaryRoot_range _
  · intro u _ g _ len _ e _
    exact ordinaryRoot_range _
  · intro u hu gap g hg e he
    exact (h.inner_values hu hg he).1
  · intro u hu gap g hg e he
    exact (h.inner_values hu hg he).2
  · intro u hu g hg len hl e he
    exact (h.tail_values hu hg hl he).1
  · intro u hu g hg len hl e he
    exact (h.tail_values hu hg hl he).2

end VG.Proof.MlDsa.AArch64.Optimized
