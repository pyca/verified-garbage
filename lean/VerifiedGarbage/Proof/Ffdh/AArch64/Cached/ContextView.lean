module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.OutputFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Context
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ReadEnv

import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring
/-! The immutable canonical input survives scratch setup and output sampling. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/ContextReads.lean`, which only this module imported.
section

/-! The reviewed canonical context supplies all native comb reads and values. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum

theorem context_readEnv {p : Parameters} {s : State} {count : Nat} {dom bs : List Byte}
 (words : p.w=Spec.Rsa.modulusWords p.k) (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p)
 (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g) (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom))
 (pointer : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w))
 (length : p.k≤dom.length) (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (dom.take p.k)) p.k=true)
 (canonical : Spec.Ffdh.generationContextAt s.mem p.ctx count p.k dom)
 (scalar : Source p.src bs s) (scalarLength : bs.length=p.k)
 (scalarOutside : ∀ i<bs.length,p.Z≤ofs p.B (p.src+BitVec.ofNat 64 i))
 (readable : ∀ i<count,InRegions (s.rd++s.wr) (p.ctx+BitVec.ofNat 64 (8*i)) 8)
 (outside : ∀ i<8*count,p.Z≤ofs p.B (p.ctx+BitVec.ofNat 64 i)) : ReadEnv p bs s := by
 have countEq : count=3+34*p.w := by rw [context_words_count canonical,words]
 have address (j i : Nat) : off p.table (8*p.w*j+8*i)=p.ctx+BitVec.ofNat 64 (8*(3+(2+j)*p.w+i)) := by
  rw [pointer]
  unfold off
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  congr 2
  ring
 have fit (j i : Nat) (hj : j<32) (hi : i<p.w) : 3+(2+j)*p.w+i<count := by
  have multiple := Nat.mul_le_mul_right p.w (show 2+j≤33 by omega)
  rw [countEq]
  omega
 refine ⟨scalar,scalarLength,scalarOutside,?_,?_,?_⟩
 · intro j hj i hi
   rw [address]
   exact readable _ (fit j i hj hi)
 · intro j hj i hi b hb
   rw [address,BitVec.add_assoc,←BitVec.ofNat_add]
   exact outside _ (by have := fit j i hj hi;omega)
 · intro j hj
   have entry := context_table_entry length valid canonical hj
   have equal : wv s.mem p.table (8*p.w*j) p.w=wv s.mem p.ctx (24+16*p.w+8*p.w*j) p.w := by
    apply wv_congr2
    intro i hi
    unfold word
    rw [address]
    congr 2
    ring
   rw [equal,words,modulus,generator,policy]
   exact entry

end VG.Proof.Ffdh.AArch64.Cached
end

end

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
