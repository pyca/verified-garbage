import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackMemory
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Mem
import VerifiedGarbage.Proof.MlDsa.Pack.Bits
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed66

/-! ## From `ResidentUnpackSpec.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (digits digits_bit bytesAt_getD map_bytes_lt)

private theorem getD_map_toNat (xs : List Byte) (i : Nat) :
    (xs.map (·.toNat)).getD i 0=(xs.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getD_eq_getElem?_getD]
  cases xs[i]? <;> rfl

/-- The overlapping-load field agrees with the target-independent FIPS bit
packing definition, including fields that straddle byte boundaries. -/
theorem fieldValue_digits (m : Mem) (a : Addr) {d i : Nat} (hd : d=18 ∨ d=20) (hi : i<256) :
    fieldValue m a d i = digits 8 ((bytesAt m a (32*d)).map (·.toNat)) / 2^(d*i) % 2^d := by
  have hw : (((m.read (a+BitVec.ofNat 64 (d*i/8)) 3).setWidth 32).extractLsb' (d*i%8) d) =
      BitVec.ofNat d (digits 8 ((bytesAt m a (32*d)).map (·.toNat)) / 2^(d*i)) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h24 : d*i%8+j<24 := by rcases hd with rfl | rfl <;> omega
    have hlen : (j+d*i)/8<32*d := by rcases hd with rfl | rfl <;> omega
    simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,
      show d*i%8+j<32 by omega,decide_true,Bool.true_and,
      BitVec.getLsbD_ofNat,Nat.testBit_div_two_pow]
    rw [getLsbD_read m 3 _ _ h24]
    simp only [BitVec.getLsbD,Nat.testBit_eq_decide_div_mod_eq]
    rw [digits_bit (by decide) (map_bytes_lt _),getD_map_toNat,bytesAt_getD _ _ hlen,Offset.add_add]
    have ha : d*i/8+(d*i%8+j)/8=(j+d*i)/8 := by omega
    have hb : (d*i%8+j)%8=(j+d*i)%8 := by omega
    rw [ha,hb]
  exact congrArg BitVec.toNat hw

/-- The completed parser meets the existing canonical polynomial meaning of
`BitUnpack`, with no new public representation or arithmetic contract. -/
theorem Parsed.poly {m input : Mem} {o a : Addr} {d : Nat} (hd : d=18 ∨ d=20)
    (h : Parsed m o input a d 256) :
    Spec.MlDsa.PolyIs m o (Spec.MlDsa.toRq (Spec.MlDsa.bitUnpack
      (bytesAt input a (32*d)) (2^(d-1)-1) (2^(d-1)))) := by
  apply VG.Proof.MlDsa.Pack.polyIs_of_toNat
  intro i hi
  have hdlen : Spec.MlDsa.bitlen (2^(d-1)-1+2^(d-1))=d := by
    rcases hd with rfl | rfl <;> decide
  have hy : digits 8 ((bytesAt input a (32*d)).map (·.toNat)) / 2^(d*i) % 2^d < Spec.MlDsa.q := by
    have hh := Nat.mod_lt (digits 8 ((bytesAt input a (32*d)).map (·.toNat)) / 2^(d*i)) (Nat.two_pow_pos d)
    rcases hd with rfl | rfl <;> change _ < 8380417 <;> omega
  rw [Spec.MlDsa.coeffAt,h i hi,fieldValue_digits input a hd hi,Spec.MlDsa.toRq,Vector.getElem_map,
    VG.Proof.MlDsa.Pack.bitUnpack_get _ _ _ hi,hdlen,VG.Proof.MlDsa.Pack.ofInt_sub hy]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentMaskBytes.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Spec.Sha3 (bytesAt)

/-- Five resident SHAKE256 blocks provide exactly the 576 or 640 bytes
consumed by the corresponding ExpandMask parser. -/
theorem stream_mask_bytes {m : Mem} {o : Addr} {Bs : List Byte} {d : Nat}
    (hd : d=18 ∨ d=20) (hlen : Bs.length=66)
    (h : Resident.StreamOutput m o 8 5 (ResidentSeed66.A0 Bs)) :
    bytesAt m o (32*d)=Spec.MlDsa.H Bs (32*d) := by
  have hb : (32*d+136-1)/136=5 := by rcases hd with rfl | rfl <;> decide
  have hc : 32*d≤136*5 := by omega
  have he : Spec.MlDsa.H Bs (32*d) =
      (Spec.Sha3.squeezeBlocks 136 (Spec.Sha3.keccakF (ResidentSeed66.A0 Bs)) 5).take (32*d) := by
    change Spec.Sha3.squeeze 136 (VG.Proof.MlKem.padded 136 Spec.Sha3.shakeSuffix Bs) (32*d)=_
    rw [ResidentSeed66.padded_A0 hlen,Spec.Sha3.squeeze,hb]
  rw [he]
  apply List.ext_getElem
  · rw [VG.Proof.MlKem.bytesAt_length,List.length_take,VG.Proof.Sha3.length_squeezeBlocks (by decide)]
    omega
  · intro j hj hj'
    rw [VG.Proof.MlKem.bytesAt_getElem,List.getElem_take]
    exact h.byte (by decide) (by rw [VG.Proof.MlKem.bytesAt_length] at hj; omega)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end
