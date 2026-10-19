module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.State
public import VerifiedGarbage.Proof.Sha3.Seed34
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.Arith

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG

def seedBytes (m : Mem) (p : Addr) (a k : Nat) : List Byte :=
  Spec.Sha3.bytesAt m p 32 ++ [BitVec.ofNat 8 (a%k), BitVec.ofNat 8 (a/k)]

theorem seedBytes_length (m : Mem) (p : Addr) (a k : Nat) :
    (seedBytes m p a k).length = 34 := by simp [seedBytes,Proof.Sha3.bytesAt_length]

theorem suffix_byte (v : BitVec 16) {j : Nat} (hj : j<8) :
    (suffix v).extractLsb' (8*j) 8 =
      if j=0 then v.extractLsb' 0 8 else if j=1 then v.extractLsb' 8 8
      else if j=2 then 0x1f else 0 := by
  rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 by omega) with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 by omega) with
      rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [suffix]

theorem nonce_low (x y : Nat) :
    (BitVec.ofNat 16 (x+256*y)).extractLsb' 0 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  omega

theorem nonce_high {x : Nat} (y : Nat) (hx : x<256) :
    (BitVec.ofNat 16 (x+256*y)).extractLsb' 8 8 = BitVec.ofNat 8 y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  omega

theorem seedBytes_get (m : Mem) (p : Addr) (a k j : Nat) :
    (seedBytes m p a k).getD j 0 = if j<32 then m (p+BitVec.ofNat 64 j)
      else if j=32 then BitVec.ofNat 8 (a%k) else if j=33 then BitVec.ofNat 8 (a/k) else 0 := by
  unfold seedBytes
  by_cases hj : j<32
  · rw [ite_eq_left hj,List.getD_eq_getElem?_getD,List.getElem?_append_left
      (by rw [Proof.Sha3.bytesAt_length]; exact hj)]
    exact Proof.MlKem.bytesAt_getD m p hj
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_append,Proof.Sha3.bytesAt_length,ite_eq_right hj]
    by_cases h32 : j=32
    · subst j; simp
    · by_cases h33 : j=33
      · subst j; simp
      · rw [ite_eq_right h32,ite_eq_right h33,List.getElem?_eq_none (by simp only [List.length_cons,List.length_nil]; omega)]
        rfl

theorem seedState_eq (m : Mem) (p : Addr) {a k : Nat} (hk : 0<k) (hk256 : k≤256) :
    seedState m p a k = Proof.Sha3.Seed34.A0 (seedBytes m p a k) := by
  have hx : a%k<256 := Nat.lt_of_lt_of_le (Nat.mod_lt a hk) hk256
  apply Proof.Sha3.ext_bytes
  intro j hj
  rw [Proof.Sha3.Seed34.byteOf_A0 (seedBytes_length m p a k) hj]
  unfold Proof.Sha3.byteOf
  rw [seedState_get m p a k (by omega)]
  by_cases h32 : j<32
  · rw [ite_eq_left (by omega : j/8<4),ite_eq_left (by omega : j<34),seedBytes_get,ite_eq_left h32]
    change (m.read (p+BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _
    rw [Mem.extractLsb'_read m _ (by omega),BitVec.add_assoc,←BitVec.ofNat_add,
      show 8*(j/8)+j%8=j by omega]
  · rw [ite_eq_right (by omega : ¬j/8<4)]
    by_cases h40 : j<40
    · rw [ite_eq_left (by omega : j/8=4),suffix_byte _ (by omega)]
      rcases (show j=32 ∨ j=33 ∨ j=34 ∨ 35≤j by omega) with h | h | h | h
      · subst j
        simp only [Nat.reduceMod,ite_eq_left (by decide : 32<34),seedBytes_get,
          ite_eq_right (by decide : ¬32<32)]
        exact nonce_low _ _
      · subst j
        simp only [Nat.reduceMod,ite_eq_right (by decide : ¬1=0),
          ite_eq_left (by decide : 33<34),seedBytes_get,ite_eq_right (by decide : ¬33<32),
          ite_eq_right (by decide : ¬33=32)]
        exact nonce_high _ hx
      · subst j; simp
      · simp (disch := omega) only [ite_eq_right]
    · rw [ite_eq_right (by omega : ¬j/8=4)]
      by_cases h20 : j/8=20
      · rw [ite_eq_left h20,Noise.pad_byte (j%8) (by omega)]
        by_cases he : j=167 <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
      · rw [ite_eq_right h20]
        simp (disch := omega) only [ite_eq_right]
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp

/-- Every emitted SHAKE128 block is the corresponding portion of the specified XOF. -/
theorem xofByte_seedState (m : Mem) (p : Addr) {a k n j : Nat}
    (hk : 0<k) (hk256 : k≤256) (hj : j<168) :
    Proof.MlKem.xofByte (seedBytes m p a k) (168*n+j) =
      Proof.Sha3.byteOf (Proof.Sha3.iterF (n+1) (seedState m p a k)) j := by
  rw [seedState_eq m p hk hk256]
  exact Proof.Sha3.Seed34.xofByte_A0 (seedBytes_length m p a k) hj

/-- This identity covers the complete 840-byte bounded sampler stream, and beyond. -/
theorem stream_seedState (m : Mem) (p : Addr) {a k : Nat}
    (hk : 0<k) (hk256 : k≤256) (i : Nat) :
    Proof.Sha3.byteOf (Proof.Sha3.iterF (i/168+1) (seedState m p a k)) (i%168) =
      Proof.MlKem.xofByte (seedBytes m p a k) i := by
  rw [←xofByte_seedState m p hk hk256 (Nat.mod_lt i (by decide))]
  congr 1
  omega

end VG.Proof.MlKem.AArch64.Paired
