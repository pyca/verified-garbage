import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTry
import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample

/-- Canonical integer represented by three source bytes. -/
def candidate (m : Mem) (p : Addr) : Nat := rnZ (m p) (m (p+1)) (m (p+2))

theorem candidate_bound (m : Mem) (p : Addr) : candidate m p<2^23 := by
  have h0 := (m p).isLt
  have h1 := (m (p+1)).isLt
  have h2 := (m (p+2)).isLt
  simp only [candidate,rnZ]
  omega

private theorem three_toNat (m : Mem) (p : Addr) :
    (m.read p 3).toNat = (m p).toNat+256*(m (p+1)).toNat+65536*(m (p+2)).toNat := by
  simp only [Mem.read,BitVec.toNat_append]
  have he : p+1+1=p+2 := by bv_omega
  rw [he]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (m p).isLt,
      ← Nat.shiftLeft_add_eq_or_of_lt (m (p+1)).isLt,
      ← Nat.shiftLeft_add_eq_or_of_lt (m (p+2)).isLt]
  simp only [Nat.shiftLeft_eq,show (0#0).toNat=0 from rfl]
  omega

theorem candidate_read (m : Mem) (p : Addr) :
    (((m.read p 3).setWidth 32) &&& 0x7fffff).toNat = candidate m p := by
  have hmask (x : BitVec 32) : (x &&& 0x7fffff).toNat=x.toNat%2^23 := by
    rw [BitVec.toNat_and,show (0x7fffff : BitVec 32).toNat=2^23-1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  rw [hmask,BitVec.toNat_setWidth_of_le (by decide),three_toNat]
  have h0 := (m p).isLt
  have h1 := (m (p+1)).isLt
  simp only [candidate,rnZ]
  omega

/-- The same candidate is obtained by the scalar unaligned word load. -/
theorem scalar_candidate (m : Mem) (p : Addr) :
    (((m.readW p 32).setWidth 64) &&& 0x7fffff).toNat=candidate m p := by
  have he : (((m.readW p 32).setWidth 64) &&& 0x7fffff)=
      ((((m.read p 3).setWidth 32) &&& 0x7fffff).setWidth 64) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_setWidth,Mem.readW]
    by_cases hb : i<23
    · have hm64 : (0x7fffff : BitVec 64).getLsbD i=true := by
        rw [show (0x7fffff : BitVec 64)=BitVec.ofNat 64 (2^23-1) from rfl]
        simp only [BitVec.getLsbD_ofNat,Nat.testBit_two_pow_sub_one,hb,hi,decide_true,Bool.and_true]
      have hm32 : (0x7fffff : BitVec 32).getLsbD i=true := by
        rw [show (0x7fffff : BitVec 32)=BitVec.ofNat 32 (2^23-1) from rfl]
        simp only [BitVec.getLsbD_ofNat,Nat.testBit_two_pow_sub_one,hb,show i<32 by omega,decide_true,Bool.and_true]
      simp only [hm64,hm32,Bool.and_true]
      rw [getLsbD_read m 4 p i (by omega),getLsbD_read m 3 p i (by omega)]
    · have hm64 : (0x7fffff : BitVec 64).getLsbD i=false := by
        rw [show (0x7fffff : BitVec 64)=BitVec.ofNat 64 (2^23-1) from rfl]
        simp only [BitVec.getLsbD_ofNat,Nat.testBit_two_pow_sub_one,hb,decide_false,Bool.and_false]
      have hm32 : (0x7fffff : BitVec 32).getLsbD i=false := by
        rw [show (0x7fffff : BitVec 32)=BitVec.ofNat 32 (2^23-1) from rfl]
        simp only [BitVec.getLsbD_ofNat,Nat.testBit_two_pow_sub_one,hb,decide_false,Bool.and_false]
      simp only [hm64,hm32,Bool.and_false]
  rw [he,BitVec.toNat_setWidth_of_le (by decide),candidate_read]

/-- Gathered and scalar fallback candidates agree exactly. -/
theorem candidates_word (m : Mem) (p : Addr) (mask : BitVec 128) {e : Nat} (he : e<4)
    (hm : vword mask e=0x7fffff) :
    (vword (candidates (m.read p 16) mask) e).toNat=candidate m (p+BitVec.ofNat 64 (3*e)) := by
  rw [candidates,vword,BitVec.extractLsb'_and]
  change ((vword (gatherValue (m.read p 16)) e) &&& vword mask e).toNat=_
  rw [hm,gather_word m p he,candidate_read]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
