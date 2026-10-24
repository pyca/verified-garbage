module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Source
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.GetElem

/-! Byte views are exact fixed-length encodings, including leading zero padding. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem source_bytesAt {ptr : Addr} {bs : List Byte} {s : State} (source : Source ptr bs s) :
 Spec.Rsa.bytesAt s.mem ptr bs.length=bs := by
 apply List.ext_getElem
 · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range]
 · intro i hi hj
   simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
   have value := source.bytes i hj
   simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some] using value

theorem source_of_bytesAt (s : State) (ptr : Addr) (k : Nat)
 (readable : ∀ i<k,InRegions (s.rd++s.wr) (ptr+BitVec.ofNat 64 i) 1) :
 Source ptr (Spec.Rsa.bytesAt s.mem ptr k) s := by
 constructor
 · intro i hi
   exact readable i (by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi)
 · intro i hi
   have inside : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
   simp only [Spec.Rsa.bytesAt,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some]

theorem source_encoding {ptr : Addr} {bs : List Byte} {s : State} (source : Source ptr bs s) :
 Spec.Rsa.bytesAt s.mem ptr bs.length=Spec.Rsa.i2osp (Spec.Rsa.os2ip bs) bs.length := by
 rw [source_bytesAt source,VG.Proof.Rsa.i2osp_os2ip]

theorem source_src {ptr B : Addr} {Z : Nat} {bs : List Byte} {s : State}
 (source : Source ptr bs s) (outside : ∀ i<bs.length,Z≤ofs B (ptr+BitVec.ofNat 64 i)) : Src s B Z ptr bs := by
 refine ⟨source.readable,?_,outside⟩
 intro i hi
 simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using source.bytes i hi

end VG.Proof.Ffdh.AArch64.Cached
