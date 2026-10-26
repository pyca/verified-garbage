module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Source
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs

/-! Byte slices retain readability and scratch separation; read-only inputs may overlap. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem src_source {s : VG.AArch64.State} {B ptr : Addr} {Z : Nat} {bs : List Byte}
 (source : Src s B Z ptr bs) : Source ptr bs s := by
 refine ⟨source.rd,?_⟩
 intro i hi
 simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using source.val i hi

theorem src_take {s : VG.AArch64.State} {B ptr : Addr} {Z : Nat} {bs : List Byte}
 (source : Src s B Z ptr bs) (n : Nat) : Src s B Z ptr (bs.take n) := by
 have view := (src_source source).take n
 refine ⟨view.readable,?_,?_⟩
 · intro i hi
   simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using view.bytes i hi
 · intro i hi
   exact source.out i (by rw [List.length_take] at hi;omega)

theorem src_drop {s : VG.AArch64.State} {B ptr : Addr} {Z : Nat} {bs : List Byte}
 (source : Src s B Z ptr bs) (n : Nat) : Src s B Z (ptr+BitVec.ofNat 64 n) (bs.drop n) := by
 have view := (src_source source).drop n
 refine ⟨view.readable,?_,?_⟩
 · intro i hi
   simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using view.bytes i hi
 · intro i hi
   have bound : n+i<bs.length := by rw [List.length_drop] at hi;omega
   simpa only [BitVec.ofNat_add,BitVec.add_assoc] using source.out (n+i) bound

theorem src_after_output {s t : VG.AArch64.State} {B ptr out : Addr} {Z k : Nat} {bs : List Byte} {rs : List VG.AArch64.Reg}
 (source : Src s B Z ptr bs) (frame : Frame [⟨B,Z⟩,⟨out,k⟩] s.mem t.mem)
 (rest : VG.Proof.MlKem.AArch64.Keep rs s t) (outside : ∀ i<bs.length,k≤ofs out (ptr+BitVec.ofNat 64 i)) :
 Src t B Z ptr bs := by
 refine ⟨?_,?_,source.out⟩
 · intro i hi;rw [rest.rd,rest.wr];exact source.rd i hi
 · intro i hi
   apply Eq.trans (frame _ ?_) (source.val i hi)
   intro r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · have sep := source.out i hi
     change ¬ofs B (ptr+BitVec.ofNat 64 i)+1≤Z
     omega
   · have sep := outside i hi
     change ¬ofs out (ptr+BitVec.ofNat 64 i)+1≤k
     omega

end VG.Proof.Ffdh.AArch64.Cached
