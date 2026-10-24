module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Bit
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Omega

/-! Read-only byte views of public domain-table prefixes. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64

theorem Source.take {p : Addr} {bs : List Byte} {s : State} (h : Source p bs s) (n : Nat) :
 Source p (bs.take n) s := by
 constructor
 · intro i hi
   have bounds : i<bs.length ∧ i<n := by simpa only [List.length_take,Nat.lt_min,and_comm] using hi
   exact h.readable i bounds.1
 · intro i hi
   have bounds : i<bs.length ∧ i<n := by simpa only [List.length_take,Nat.lt_min,and_comm] using hi
   rw [h.bytes i bounds.1]
   simp only [List.getD_eq_getElem?_getD,List.getElem?_take,ite_eq_left bounds.2]

theorem Source.drop {p : Addr} {bs : List Byte} {s : State} (h : Source p bs s) (n : Nat) :
 Source (p+BitVec.ofNat 64 n) (bs.drop n) s := by
 constructor
 · intro i hi
   have inside : n+i<bs.length := by rw [List.length_drop] at hi;omega
   simpa only [BitVec.ofNat_add,BitVec.add_assoc] using h.readable (n+i) inside
 · intro i hi
   have inside : n+i<bs.length := by rw [List.length_drop] at hi;omega
   rw [BitVec.add_assoc,←BitVec.ofNat_add,h.bytes (n+i) inside]
   simp only [List.getD_eq_getElem?_getD,List.getElem?_drop]

theorem Source.after_outside {p B : Addr} {bs : List Byte} {s t : State} {rs : List VG.AArch64.Reg} {o n : Nat}
 (h : Source p bs s) (frame : VG.Proof.Bignum.Outside B o n s.mem t.mem)
 (rest : VG.Proof.MlKem.AArch64.Keep rs s t)
 (separate : ∀ i<bs.length,o+n≤VG.Proof.Bignum.ofs B (p+BitVec.ofNat 64 i)) : Source p bs t := by
 constructor
 · intro i hi;rw [rest.rd,rest.wr];exact h.readable i hi
 · intro i hi
   exact (frame _ (Or.inr (separate i hi))).trans (h.bytes i hi)

end VG.Proof.Ffdh.AArch64.Cached
