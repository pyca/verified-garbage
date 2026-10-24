module

public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Frame
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring

/-! Native 64-bit reads of the already reviewed, backend-independent context. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

theorem context_words {m : Mem} {ctx : Addr} {count k : Nat} {dom : List Byte}
 (length : k≤dom.length) (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (dom.take k)) k=true)
 (canonical : Spec.Ffdh.generationContextAt m ctx count k dom) :
 Spec.Rsa.wordsAt m ctx count=VG.Proof.Ffdh.generationValues k dom := by
 have equation := VG.Proof.Ffdh.generationPrecompute_eq length valid
 rw [canonical.2] at equation
 exact Option.some.inj equation

theorem context_words_count {m : Mem} {ctx : Addr} {count k : Nat} {dom : List Byte}
 (canonical : Spec.Ffdh.generationContextAt m ctx count k dom) :
 count=3+34*Spec.Rsa.modulusWords k := by
 rw [canonical.1]
 simp only [Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
  Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth]
 omega

theorem context_header {m : Mem} {ctx : Addr} {count k j : Nat} {dom : List Byte}
 (length : k≤dom.length) (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (dom.take k)) k=true)
 (canonical : Spec.Ffdh.generationContextAt m ctx count k dom) (hj : j<3) :
 m.readW (ctx+BitVec.ofNat 64 (8*j)) 64=
 ([BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)),
  BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)+7)/8),
  BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)))] : List (BitVec 64)).getD j 0 := by
 have words := congrArg (fun xs : List (BitVec 64) => xs[j]?) (context_words length valid canonical)
 have count3 : 3≤count := by rw [context_words_count canonical];omega
 simp only [Spec.Rsa.wordsAt,List.getElem?_map,List.getElem?_range (by omega : j<count),Option.map_some] at words
 have heads := congrArg (fun xs : List (BitVec 64) => xs[j]?) (VG.Proof.Ffdh.generationValues_headers k dom)
 simp only [List.getElem?_take,ite_eq_left hj] at heads
 rw [heads] at words
 have cases : j=0 ∨ j=1 ∨ j=2 := by omega
 rcases cases with rfl | rfl | rfl <;> simpa using words

/-- Entry a is a complete reduced Montgomery residue with no backend pointers. -/
theorem context_table_entry {m : Mem} {ctx : Addr} {count k a : Nat} {dom : List Byte}
 (length : k≤dom.length) (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (dom.take k)) k=true)
 (canonical : Spec.Ffdh.generationContextAt m ctx count k dom) (ha : a<32) :
 let w := Spec.Rsa.modulusWords k
 let P := (Spec.Ffdh.domainOf k dom).p
 let G := (Spec.Ffdh.domainOf k dom).g
 let N := Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)
 wv m ctx (24+16*w+8*w*a) w=
  Spec.Rsa.powMod G (Spec.Rsa.FixedBaseComb.exponent N a) P * 2^(64*w)%P := by
 dsimp only
 let w := Spec.Rsa.modulusWords k
 let E := Spec.Rsa.powMod (Spec.Ffdh.domainOf k dom).g
  (Spec.Rsa.FixedBaseComb.exponent (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)) a)
  (Spec.Ffdh.domainOf k dom).p *2^(64*w)%(Spec.Ffdh.domainOf k dom).p
 have pBound : (Spec.Ffdh.domainOf k dom).p<2^(64*w) := by
  have bound := VG.Proof.Bignum.os2ip_lt (dom.take k)
  have len : (dom.take k).length=k := by simp only [List.length_take];omega
  rw [len,VG.Proof.Bignum.pow256_eq] at bound
  exact Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by dsimp [w,Spec.Rsa.modulusWords];omega))
 have pPositive : 0<(Spec.Ffdh.domainOf k dom).p := by
  have facts := valid
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,decide_eq_true_eq] at facts
  change 0<Spec.Rsa.os2ip (dom.take k)
  omega
 have eBound : E<2^(64*w) := Nat.lt_trans (Nat.mod_lt _ pPositive) pBound
 change wv m ctx (24+16*w+8*w*a) w=E
 rw [←Nat.mod_eq_of_lt eBound]
 apply wv_of_words
 intro i hi
 let index := 3+(2+a)*w+i
 have indexFit : index<count := by
  have hcount := context_words_count canonical
  have aW := Nat.mul_le_mul_right w (show 2+a≤33 by omega)
  dsimp [index,w] at *
  omega
 have entry := congrArg (fun xs : List (BitVec 64) => xs[i]?) (VG.Proof.Ffdh.generationValues_entry k dom a ha)
 have hik : i<Spec.Rsa.modulusWords k := hi
 simp only [List.getElem?_take,ite_eq_left hik,List.getElem?_drop,Spec.Rsa.toWords,
  List.getElem?_map,List.getElem?_range hik,Option.map_some] at entry
 have read := congrArg (fun xs : List (BitVec 64) => xs[index]?) (context_words length valid canonical)
 simp only [Spec.Rsa.wordsAt,List.getElem?_map,List.getElem?_range indexFit,Option.map_some] at read
 change some (m.readW (off ctx (8*index)) 64)=_ at read
 dsimp only [index,w] at read
 rw [entry] at read
 have offset : 24+16*w+8*w*a+8*i=8*index := by dsimp [index];ring
 change (m.readW (off ctx (24+16*w+8*w*a+8*i)) 64).toNat=_
 rw [offset,Option.some.inj read,BitVec.toNat_ofNat]

end VG.Proof.Ffdh.AArch64.Cached
