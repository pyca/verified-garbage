import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailOutput
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailHash
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident

theorem ratePairs_word {m : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    (h : RatePairs m a n A) {i : Nat} (hi : i<2*n) :
    m.readW (a+BitVec.ofNat 64 (8*i)) 64=A[i]! := by
  have hp := h (i/2) (by omega)
  have hv := congrArg (fun v => vdword v (i%2)) hp
  rw [vdword_read16 _ _ (by omega)] at hv
  rcases (show i%2=0 ∨ i%2=1 by omega) with hm|hm
  · rw [hm,vdword_ofVDwords_0] at hv
    simpa only [BitVec.add_assoc,BitVec.ofNat_add_ofNat,
      show 16*(i/2)+8*0=8*i by omega,show 2*(i/2)=i by omega] using hv
  · rw [hm,vdword_ofVDwords_1] at hv
    simpa only [BitVec.add_assoc,BitVec.ofNat_add_ofNat,
      show 16*(i/2)+8*1=8*i by omega,show 2*(i/2)+1=i by omega] using hv

theorem ratePairs_byte {m : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    (h : RatePairs m a n A) {j : Nat} (hj : j<16*n) :
    m (a+BitVec.ofNat 64 j)=Proof.Sha3.byteOf A j := by
  have hw := ratePairs_word h (i:=j/8) (by omega)
  have he := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) hw
  change (m.read (a+BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8=_ at he
  rw [Mem.extractLsb'_read m _ (by omega)] at he
  rw [BitVec.add_assoc,← BitVec.ofNat_add,show 8*(j/8)+j%8=j by omega] at he
  exact he

theorem ratePairs_bytes {m : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    (h : RatePairs m a n A) (hn : n≤12) :
    Spec.Sha3.bytesAt m a (16*n)=(Spec.Sha3.toBytes A).take (16*n) := by
  apply List.ext_getElem
  · rw [Proof.Sha3.bytesAt_length,List.length_take,Proof.Sha3.length_toBytes]
    omega
  · intro j hj hj'
    rw [Proof.Sha3.bytesAt_length] at hj
    rw [Proof.MlKem.bytesAt_getElem,List.getElem_take,Proof.Sha3.toBytes_getElem _ (by omega)]
    exact ratePairs_byte h hj

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
