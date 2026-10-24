module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Source
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecord
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Omega

/-! A read-only vetted-domain record and the separation needed for a matched cap store. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure PolicyRecordAt (B rec : Addr) (g : Policy.Group) (s : State) : Prop where
 lenPositive : 0<g.len
 lenFit : g.len<2^32
 bitsFit : g.bits<2^32
 readLen : InRegions (s.rd++s.wr) rec 4
 readBits : InRegions (s.rd++s.wr) (off rec 4) 4
 length : s.mem.readW rec 32=BitVec.ofNat 32 g.len
 bits : s.mem.readW (off rec 4) 32=BitVec.ofNat 32 g.bits
 source : Source (off rec 8) g.domain s
 outside : ∀ b<8+3*g.len,8*sBits+8≤ofs B (rec+BitVec.ofNat 64 b)

theorem PolicyRecordAt.separate {B rec : Addr} {g : Policy.Group} {s : State}
 (h : PolicyRecordAt B rec g s) : ∀ b<4,8*sBits+8≤ofs B (rec+BitVec.ofNat 64 b) :=
 fun b hb => h.outside b (by omega)

theorem policyDomain_length (g : Policy.Group) : g.domain.length=3*g.len := by
 simp only [Policy.Group.domain,List.length_append,VG.Proof.Rsa.i2osp_length]
 omega

theorem PolicyRecordAt.after_mem {B rec : Addr} {g : Policy.Group} {s t : State} {rs : List Reg}
 (h : PolicyRecordAt B rec g s) (mem : t.mem=s.mem) (rest : Keep rs s t) : PolicyRecordAt B rec g t :=
 ⟨h.lenPositive,h.lenFit,h.bitsFit,by rw [rest.rd,rest.wr];exact h.readLen,
  by rw [rest.rd,rest.wr];exact h.readBits,by rw [mem];exact h.length,by rw [mem];exact h.bits,
  h.source.of_mem mem rest,h.outside⟩

theorem sub_zero_iff {a b : Nat} (ha : a<2^64) (hb : b<2^64) :
 (BitVec.ofNat 64 a-BitVec.ofNat 64 b == 0#64)=decide (a=b) := by
 apply Bool.eq_iff_iff.mpr
 simp only [beq_iff_eq,decide_eq_true_eq]
 constructor
 · intro eq
   have number := congrArg BitVec.toNat eq
   simp only [BitVec.toNat_sub,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at number
   omega
 · rintro rfl
   exact BitVec.sub_self _

end VG.Proof.Ffdh.AArch64.Cached
