module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ContextReads
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.OutputFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! The immutable canonical input survives scratch setup and output sampling. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

structure ContextView (B : Addr) (Z : Nat) (ctx : Addr) (count k : Nat) (dom : List Byte) (s : State) : Prop where
 canonical : Spec.Ffdh.generationContextAt s.mem ctx count k dom
 readable : ∀ i<count,InRegions (s.rd++s.wr) (ctx+BitVec.ofNat 64 (8*i)) 8
 outside : ∀ i<8*count,Z≤ofs B (ctx+BitVec.ofNat 64 i)

theorem ContextView.after_inscr {s t : State} {B ctx : Addr} {Z count k : Nat} {dom : List Byte} {rs : List Reg}
 (view : ContextView B Z ctx count k dom s) (frame : InScr B Z s.mem t.mem) (rest : Keep rs s t) :
 ContextView B Z ctx count k dom t := by
 have words : Spec.Rsa.wordsAt t.mem ctx count=Spec.Rsa.wordsAt s.mem ctx count := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.wordsAt,List.length_map,List.length_range]
  · intro i hi _
    have bound : i<count := by simpa only [Spec.Rsa.wordsAt,List.length_map,List.length_range] using hi
    simp only [Spec.Rsa.wordsAt,List.getElem_map,List.getElem_range]
    apply Mem.readW_congr
    intro j hj
    have outside := view.outside (8*i+j) (by omega)
    exact frame _ (by simpa only [BitVec.ofNat_add,BitVec.add_assoc] using outside)
 refine ⟨?_,?_,view.outside⟩
 · unfold Spec.Ffdh.generationContextAt
   rw [words]
   exact view.canonical
 · intro i hi;rw [rest.rd,rest.wr];exact view.readable i hi

theorem ContextView.after_output {s t : State} {B ctx out : Addr} {Z count k : Nat} {dom : List Byte} {rs : List Reg}
 (view : ContextView B Z ctx count k dom s) (frame : Frame [⟨B,Z⟩,⟨out,k⟩] s.mem t.mem) (rest : Keep rs s t)
 (outside : ∀ i<8*count,k≤ofs out (ctx+BitVec.ofNat 64 i)) : ContextView B Z ctx count k dom t := by
 have words : Spec.Rsa.wordsAt t.mem ctx count=Spec.Rsa.wordsAt s.mem ctx count := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.wordsAt,List.length_map,List.length_range]
  · intro i hi _
    have bound : i<count := by simpa only [Spec.Rsa.wordsAt,List.length_map,List.length_range] using hi
    simp only [Spec.Rsa.wordsAt,List.getElem_map,List.getElem_range]
    apply Mem.readW_congr
    intro j hj
    apply frame
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · have sep := view.outside (8*i+j) (by omega)
      have h : Z≤ofs B (ctx+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 j) :=
       by simpa only [BitVec.ofNat_add,BitVec.add_assoc] using sep
      change ¬ofs B (ctx+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 j)+1≤Z
      omega
    · have sep := outside (8*i+j) (by omega)
      have h : k≤ofs out (ctx+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 j) :=
       by simpa only [BitVec.ofNat_add,BitVec.add_assoc] using sep
      change ¬ofs out (ctx+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 j)+1≤k
      omega
 refine ⟨?_,?_,view.outside⟩
 · unfold Spec.Ffdh.generationContextAt
   rw [words]
   exact view.canonical
 · intro i hi;rw [rest.rd,rest.wr];exact view.readable i hi

end VG.Proof.Ffdh.AArch64.Cached
