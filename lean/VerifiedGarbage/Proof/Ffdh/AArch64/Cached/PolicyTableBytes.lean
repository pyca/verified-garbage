module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTable
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecordBytes
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Omega

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
