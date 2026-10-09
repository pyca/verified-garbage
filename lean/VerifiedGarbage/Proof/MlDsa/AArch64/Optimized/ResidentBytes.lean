import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentPair
import VerifiedGarbage.Proof.Sha3.Stream

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64

/-- The vectorized rate block has the same little-endian words as scalar
SHAKE serialization. -/
theorem RateBlock.word {m : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    (h : RateBlock m a n A) {i : Nat} (hi : i < 2*n+1) :
    m.readW (a+BitVec.ofNat 64 (8*i)) 64 = A[i]! := by
  by_cases he : i = 2*n
  · subst i
    simpa only [show 8*(2*n)=16*n by omega] using h.2
  · have hp := h.1 (i/2) (by omega)
    have hv := congrArg (fun v => vdword v (i%2)) hp
    rw [vdword_read16 _ _ (by omega)] at hv
    rcases (show i%2=0 ∨ i%2=1 by omega) with hm | hm
    · rw [hm,vdword_ofVDwords_0] at hv
      simpa only [BitVec.add_assoc,BitVec.ofNat_add_ofNat,
        show 16*(i/2)+8*0=8*i by omega,show 2*(i/2)=i by omega] using hv
    · rw [hm,vdword_ofVDwords_1] at hv
      simpa only [BitVec.add_assoc,BitVec.ofNat_add_ofNat,
        show 16*(i/2)+8*1=8*i by omega,show 2*(i/2)+1=i by omega] using hv

/-- The caller's byte parser sees exactly the specification's state bytes. -/
theorem RateBlock.byte {m : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    (h : RateBlock m a n A) {j : Nat} (hj : j < 16*n+8) :
    m (a+BitVec.ofNat 64 j) = VG.Proof.Sha3.byteOf A j := by
  have hw := h.word (i := j/8) (by omega)
  have he := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) hw
  change (m.read (a+BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _ at he
  rw [Mem.extractLsb'_read m _ (by omega)] at he
  rw [BitVec.add_assoc,← BitVec.ofNat_add,show 8*(j/8)+j%8=j by omega] at he
  exact he

theorem permuted_eq_iterF (A : Spec.Sha3.State) (j : Nat) :
    permuted A j = VG.Proof.Sha3.iterF j A := by
  induction j with
  | zero => rfl
  | succ j ih => rw [permuted,VG.Proof.Sha3.iterF_succ,ih]

/-- Complete byte serialization agrees with the SHAKE specification, starting
with the first resident permutation. The caller supplies the absorbed state. -/
theorem StreamOutput.byte {m : Mem} {a : Addr} {n blocks : Nat} {A : Spec.Sha3.State}
    (h : StreamOutput m a n blocks A) (hn : n ≤ 10) {j : Nat}
    (hj : j < (16*n+8)*blocks) :
    m (a+BitVec.ofNat 64 j) =
      (Spec.Sha3.squeezeBlocks (16*n+8) (Spec.Sha3.keccakF A) blocks)[j]'(by
        rw [VG.Proof.Sha3.length_squeezeBlocks (by omega)]; exact hj) := by
  have hk : j/(16*n+8) < blocks := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa only [Nat.mul_comm] using hj)
  have hb := (h _ hk).byte (j := j%(16*n+8)) (Nat.mod_lt _ (by omega))
  rw [BitVec.add_assoc,← BitVec.ofNat_add,Nat.div_add_mod] at hb
  rw [hb,VG.Proof.Sha3.getElem_squeezeBlocks (by omega) (by omega),permuted_eq_iterF,
    VG.Proof.Sha3.iterF_keccakF]

end VG.Proof.MlDsa.AArch64.Optimized.Resident
