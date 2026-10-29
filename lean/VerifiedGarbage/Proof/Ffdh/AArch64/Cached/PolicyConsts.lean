module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyMath
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecordEnv
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTable

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.CallLay
/-! The emitted native quadwords contain exactly the reviewed public vetted-group table. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PolicyRecordBytes.lean`, which only this module imported.
section

/-! Decode a serialized vetted-domain record at a native 64-bit address. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

private theorem decode_wordBytes (x : Nat) (fit : x<2^32) :
 VG.Proof.X25519.leNum (Policy.wordBytes x)=x := by
 simp only [Policy.wordBytes,List.range_succ,List.range_zero,List.map_append,List.map_cons,
  List.map_nil,List.nil_append,Nat.reduceMul,Nat.reducePow,Nat.div_one]
 simp only [List.cons_append,List.nil_append,VG.Proof.X25519.leNum,BitVec.toNat_ofNat,Nat.mul_zero,Nat.add_zero]
 omega

private theorem read_wordBytes {m : Mem} {p : Addr} {x : Nat}
 (fit : x<2^32) (bytes : Spec.Rsa.bytesAt m p 4=Policy.wordBytes x) :
 m.readW p 32=BitVec.ofNat 32 x := by
 apply BitVec.eq_of_toNat_eq
 have number := congrArg VG.Proof.X25519.leNum bytes
 change VG.Proof.X25519.leNum (Spec.X25519.bytesAt m p 4)=_ at number
 rw [VG.Proof.X25519.leNum_bytesAt_32bit,decode_wordBytes x fit] at number
 simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit] using number

theorem policyGroupBytes_length (g : Policy.Group) : g.bytes.length=8+3*g.len := by
 simp only [Policy.Group.bytes,Policy.wordBytes,List.length_append,List.length_map,List.length_range,
  policyDomain_length]

theorem policyRecordOfBytes {s : State} {B p : Addr} {g : Policy.Group}
 (positive : 0<g.len) (lenFit : g.len<2^32) (bitsFit : g.bits<2^32)
 (fit : g.bytes.length<2^64) (read : InRegions (s.rd++s.wr) p g.bytes.length)
 (bytes : Spec.Rsa.bytesAt s.mem p g.bytes.length=g.bytes)
 (separate : ∀ b<g.bytes.length,8*sBits+8≤ofs B (p+BitVec.ofNat 64 b)) : PolicyRecordAt B p g s := by
 have length := policyGroupBytes_length g
 have wordLength (x : Nat) : (Policy.wordBytes x).length=4 := by
  simp only [Policy.wordBytes,List.length_map,List.length_range]
 have headLen : (g.bytes.drop 0).take 4=Policy.wordBytes g.len := by
  simp only [Policy.Group.bytes,List.drop_zero,List.append_assoc,List.take_left',wordLength]
 have headBits : (g.bytes.drop 4).take 4=Policy.wordBytes g.bits := by
  rw [Policy.Group.bytes,List.append_assoc,←wordLength g.len,List.drop_left]
  simp only [List.take_left',wordLength]
 have domain : (g.bytes.drop 8).take (3*g.len)=g.domain := by
  rw [Policy.Group.bytes,show 8=(Policy.wordBytes g.len++Policy.wordBytes g.bits).length by
   simp only [List.length_append,wordLength],List.drop_left]
  rw [←policyDomain_length,List.take_length]
 have slice (d n : Nat) (part : d+n≤g.bytes.length) :
  Spec.Rsa.bytesAt s.mem (off p d) n=(g.bytes.drop d).take n := by
  rw [←VG.Proof.Dsa.bytesAt_slice s.mem p part,bytes]
 have reads (d n : Nat) (part : d+n≤g.bytes.length) : InRegions (s.rd++s.wr) (off p d) n :=
  VG.CallLay.inRegions_sub read part fit
 have view : Spec.Rsa.bytesAt s.mem (off p 8) g.domain.length=g.domain := by
  rw [policyDomain_length]
  exact (slice 8 (3*g.len) (by omega)).trans domain
 refine ⟨positive,lenFit,bitsFit,?_,reads 4 4 (by omega),?_,?_,?_,fun b hb => separate b (by omega)⟩
 · simpa only [off,BitVec.add_zero] using reads 0 4 (by omega)
 · apply read_wordBytes lenFit
   simpa only [off,BitVec.add_zero,headLen] using slice 0 4 (by omega)
 · exact read_wordBytes bitsFit ((slice 4 4 (by omega)).trans headBits)
 · constructor
   · intro i hi
     have rd := reads (8+i) 1 (by rw [policyDomain_length] at hi;omega)
     simpa only [off,BitVec.add_assoc,BitVec.ofNat_add] using rd
   · intro i hi
     have byte := congrArg (fun xs : List Byte => xs[i]?) view
     simp only [Spec.Rsa.bytesAt,List.getElem?_map,List.getElem?_range hi,Option.map_some,
      List.getElem?_eq_getElem hi] at byte
     rw [Option.some.inj byte]
     exact List.getElem_eq_getD 0

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PolicyTableBytes.lean`, which only this module imported.
section

/-! The serialized byte table gives the execution invariant at every record boundary. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem policyTableOfBytes {s : State} {B p : Addr} {gs : List Policy.Group}
 (fit : (gs.flatMap Policy.Group.bytes).length<2^64)
 (read : InRegions (s.rd++s.wr) p (gs.flatMap Policy.Group.bytes).length)
 (bytes : Spec.Rsa.bytesAt s.mem p (gs.flatMap Policy.Group.bytes).length=gs.flatMap Policy.Group.bytes)
 (valid : ∀ g∈gs,0<g.len ∧ g.len<2^32 ∧ g.bits<2^32)
 (safe : ∀ i<(gs.flatMap Policy.Group.bytes).length,8*sBits+8≤ofs B (p+BitVec.ofNat 64 i)) :
 PolicyTableAt B p gs s := by
 induction gs generalizing p with
 | nil => trivial
 | cons g gs ih =>
   have vg := valid g (by simp)
   have length := policyGroupBytes_length g
   have total : ((g::gs).flatMap Policy.Group.bytes).length=
     g.bytes.length+(gs.flatMap Policy.Group.bytes).length := by
    simp only [List.flatMap_cons,List.length_append]
   have subRead (d n : Nat) (part : d+n≤((g::gs).flatMap Policy.Group.bytes).length) :
     InRegions (s.rd++s.wr) (off p d) n := VG.CallLay.inRegions_sub read part fit
   have subBytes (d n : Nat) (part : d+n≤((g::gs).flatMap Policy.Group.bytes).length) :
     Spec.Rsa.bytesAt s.mem (off p d) n=(((g::gs).flatMap Policy.Group.bytes).drop d).take n := by
    rw [←VG.Proof.Dsa.bytesAt_slice s.mem p part,bytes]
   have headRead : InRegions (s.rd++s.wr) p g.bytes.length := by
    simpa only [off,BitVec.add_zero] using subRead 0 g.bytes.length (by omega)
   have headBytes : Spec.Rsa.bytesAt s.mem p g.bytes.length=g.bytes := by
    simpa only [off,BitVec.add_zero,List.drop_zero,List.flatMap_cons,List.take_left] using
     subBytes 0 g.bytes.length (by omega)
   have head := policyRecordOfBytes vg.1 vg.2.1 vg.2.2 (by omega) headRead headBytes
    (fun b hb => safe b (by omega))
   refine ⟨head,?_⟩
   have tailRead := subRead g.bytes.length (gs.flatMap Policy.Group.bytes).length (by omega)
   have tailBytes := subBytes g.bytes.length (gs.flatMap Policy.Group.bytes).length (by omega)
   simp only [List.flatMap_cons,List.drop_left,List.take_length] at tailBytes
   rw [length] at tailRead tailBytes
   refine ih (by omega) tailRead tailBytes (fun a ha => valid a (by simp [ha])) ?_
   intro i hi
   have outside := safe (g.bytes.length+i) (by omega)
   rw [length] at outside
   simpa only [off,BitVec.add_assoc,BitVec.ofNat_add] using outside

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

private theorem singletonRead {name : String} {words : List (BitVec 64)} {st : Nat} {s : State}
 (hc : ConstsOk [(name,words)] st s) : InRegions (s.rd++s.wr) (s.syms name) (8*words.length) := by
 have member : (⟨s.syms name,8*words.length⟩ : Region)∈s.rd := by
  apply List.mem_of_mem_drop
  rw [hc.1]
  exact List.mem_cons_self
 exact ⟨_,List.mem_append_left _ member,Region.contains_self _ _⟩

private theorem singletonRegion {name : String} {words : List (BitVec 64)} {st : Nat} {s : State}
 (hc : ConstsOk [(name,words)] st s) :
 (s.syms name).toNat+8*words.length≤2^64 ∧
 (∀ r∈s.wr,(⟨s.syms name,8*words.length⟩ : Region).Disjoint r) := by
 have h := hc.2.2.1 (⟨s.syms name,8*words.length⟩ : Region) List.mem_cons_self
 exact ⟨h.1,h.2.1⟩

private theorem singletonHeld {name : String} {words : List (BitVec 64)} {st : Nat} {s : State}
 (hc : ConstsOk [(name,words)] st s) :
 ∀ j<words.length,s.mem.readW (s.syms name+BitVec.ofNat 64 (8*j)) 64=words.getD j 0 :=
 fun j hj => hc.2.1 (name,words) List.mem_cons_self j hj

private theorem constRead {st : Nat} {s : State} (hc : ConstsOk Policy.tableConsts st s) :
 InRegions (s.rd++s.wr) (s.syms Policy.tableSym) Policy.tableBytes.length := by
 have read := singletonRead hc
 simpa only [Policy.tableWords_length,Policy.tableBytes_length] using read

private theorem constBytes {st : Nat} {s : State} (hc : ConstsOk Policy.tableConsts st s) :
 Spec.Rsa.bytesAt s.mem (s.syms Policy.tableSym) Policy.tableBytes.length=Policy.tableBytes := by
 apply List.ext_getElem
 · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range]
 · intro i hi hj
   simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
   have byte :=PolicyFacts.table_held_byte (singletonHeld hc) (i:=i) hj
   rw [byte]
   exact (List.getElem_eq_getD (h:=hj) 0).symm

theorem policyConsts_table {s : State} {B : Addr} {Z st : Nat}
 (hc : ConstsOk Policy.tableConsts st s) (scratch : Scr s B Z) (room : 256≤Z) :
 PolicyTableAt B (s.syms Policy.tableSym) Policy.groups s := by
 have region := singletonRegion hc
 have readable := constRead hc
 have bytes := constBytes hc
 have length := Policy.tableBytes_length
 have wordLength := Policy.tableWords_length
 have safe : ∀ i<Policy.tableBytes.length,8*VG.Impl.Ffdh.AArch64.Cached.sBits+8≤
    ofs B (s.syms Policy.tableSym+BitVec.ofNat 64 i) := by
  intro i hi
  obtain ⟨r,hr,contains⟩ := scratch.region (d:=0) (n:=Z) (by omega) (by omega)
  have containsB : r.Contains B Z := by simpa only [off,BitVec.add_zero] using contains
  have outside : Z≤ofs B (s.syms Policy.tableSym+BitVec.ofNat 64 i) := by
   by_contra no
   have within : ofs B (s.syms Policy.tableSym+BitVec.ofNat 64 i)<Z := by omega
   exact (region.2 r hr) _ (Offset.contains_base _ (by rw [wordLength];rw [length] at hi;omega)
    (by rw [length] at hi;omega)) (containsB.byte within)
  unfold VG.Impl.Ffdh.AArch64.Cached.sBits
  omega
 refine policyTableOfBytes (by rw [←show Policy.tableBytes=Policy.groups.flatMap Policy.Group.bytes from rfl,length];decide)
  readable bytes ?_ safe
 intro g hg
 simp only [Policy.groups,List.mem_cons,List.not_mem_nil,or_false] at hg
 rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

end VG.Proof.Ffdh.AArch64.Cached
