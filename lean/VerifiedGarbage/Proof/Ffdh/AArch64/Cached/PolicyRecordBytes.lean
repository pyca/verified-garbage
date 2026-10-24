module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecordEnv
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Omega

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
