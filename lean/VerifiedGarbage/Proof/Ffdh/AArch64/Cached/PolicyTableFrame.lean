module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTable
import VerifiedGarbage.Proof.Framework.Omega

/-! Writing the scalar width cannot change the read-only vetted-group table. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem PolicyRecordAt.after_header {B rec : Addr} {g : Policy.Group} {s t : State} {rs : List Reg}
 (h : PolicyRecordAt B rec g s) (frame : Outside B (8*sBits) 8 s.mem t.mem)
 (rest : Keep rs s t) : PolicyRecordAt B rec g t := by
 refine ⟨h.lenPositive,h.lenFit,h.bitsFit,?_,?_,?_,?_,?_,h.outside⟩
 · rw [rest.rd,rest.wr];exact h.readLen
 · rw [rest.rd,rest.wr];exact h.readBits
 · apply Eq.trans (Mem.readW_congr fun i hi => frame _ (Or.inr (h.outside i (by omega)))) h.length
 · apply Eq.trans (Mem.readW_congr fun i hi => frame _ (Or.inr ?_)) h.bits
   have bound := h.outside (4+i) (by omega)
   simpa only [off,BitVec.add_assoc,BitVec.ofNat_add] using bound
 · constructor
   · intro i hi;rw [rest.rd,rest.wr];exact h.source.readable i hi
   · intro i hi
     have bound := h.outside (8+i) (by rw [policyDomain_length] at hi;omega)
     have equal : t.mem (off rec 8+BitVec.ofNat 64 i)=s.mem (off rec 8+BitVec.ofNat 64 i) :=
      frame _ (Or.inr (by simpa only [off,BitVec.add_assoc,BitVec.ofNat_add] using bound))
     exact equal.trans (h.source.bytes i hi)

theorem PolicyTableAt.after_header {B p : Addr} {gs : List Policy.Group} {s t : State} {rs : List Reg}
 (h : PolicyTableAt B p gs s) (frame : Outside B (8*sBits) 8 s.mem t.mem)
 (rest : Keep rs s t) : PolicyTableAt B p gs t := by
 induction gs generalizing p with
 | nil => trivial
 | cons g gs ih => exact ⟨h.1.after_header frame rest,ih h.2⟩

theorem PolicyRecordAt.after_belowBits {B rec : Addr} {g : Policy.Group} {s t : State} {rs : List Reg} {d n : Nat}
 (h : PolicyRecordAt B rec g s) (frame : Outside B d n s.mem t.mem)
 (rest : Keep rs s t) (below : d+n≤8*sBits+8) : PolicyRecordAt B rec g t := by
 refine ⟨h.lenPositive,h.lenFit,h.bitsFit,?_,?_,?_,?_,?_,h.outside⟩
 · rw [rest.rd,rest.wr];exact h.readLen
 · rw [rest.rd,rest.wr];exact h.readBits
 · apply Eq.trans (Mem.readW_congr fun i hi => frame _ (Or.inr (Nat.le_trans below (h.outside i (by omega))))) h.length
 · apply Eq.trans (Mem.readW_congr fun i hi => frame _ (Or.inr ?_)) h.bits
   have bound := h.outside (4+i) (by omega)
   simpa only [off,BitVec.add_assoc,BitVec.ofNat_add] using (Nat.le_trans below bound)
 · constructor
   · intro i hi;rw [rest.rd,rest.wr];exact h.source.readable i hi
   · intro i hi
     have bound := h.outside (8+i) (by rw [policyDomain_length] at hi;omega)
     have equal : t.mem (off rec 8+BitVec.ofNat 64 i)=s.mem (off rec 8+BitVec.ofNat 64 i) :=
      frame _ (Or.inr (by simpa only [off,BitVec.add_assoc,BitVec.ofNat_add] using (Nat.le_trans below bound)))
     exact equal.trans (h.source.bytes i hi)

theorem PolicyTableAt.after_belowBits {B p : Addr} {gs : List Policy.Group} {s t : State} {rs : List Reg} {d n : Nat}
 (h : PolicyTableAt B p gs s) (frame : Outside B d n s.mem t.mem)
 (rest : Keep rs s t) (below : d+n≤8*sBits+8) : PolicyTableAt B p gs t := by
 induction gs generalizing p with
 | nil => trivial
 | cons g gs ih => exact ⟨h.1.after_belowBits frame rest below,ih h.2⟩

end VG.Proof.Ffdh.AArch64.Cached
