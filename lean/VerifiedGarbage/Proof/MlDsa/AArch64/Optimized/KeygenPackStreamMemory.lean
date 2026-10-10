import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFields
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten

/-! ## From `KeygenPackStream.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlDsa.Pack

def acc64 (G d j : Nat) : Nat := G%2^(d*j)/2^(64*(d*j/64))

theorem acc64_lt (G d j : Nat) : acc64 G d j<2^(d*j%64) := by
  have h := mod_div_lt G (d*j) (64*(d*j/64))
  simpa only [acc64,show d*j-64*(d*j/64)=d*j%64 by omega] using h

theorem add64 (G d j : Nat) :
    acc64 G d j+(G/2^(d*j)%2^d)*2^(d*j%64)=
      G%2^(d*(j+1))/2^(64*(d*j/64)) := by
  unfold acc64
  rw [Nat.mul_succ,mod_two_pow_add,two_pow_split (show 64*(d*j/64)≤d*j by omega),
    show d*j-64*(d*j/64)=d*j%64 by omega,Nat.mul_assoc,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.mul_comm (2^(d*j%64))]

theorem ofNat_shift (v sh : Nat) :
    (BitVec.ofNat 64 v<<<sh)=BitVec.ofNat 64 (v*2^sh) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,Nat.mod_mul_mod]

theorem joined_nat (d j a v : Nat) (ha : a<2^(d*j%64)) :
    joined d j (BitVec.ofNat 64 a) (BitVec.ofNat 64 v)=
      BitVec.ofNat 64 (a+v*2^(d*j%64)) := by
  unfold joined
  split
  · rename_i h
    have hz : a=0 := by simpa only [h,Nat.pow_zero,Nat.lt_one_iff] using ha
    simp only [hz,h,Nat.pow_zero,Nat.mul_one,Nat.zero_add]
  · rw [ofNat_shift,←BitVec.ofNat_or,Nat.or_comm,
      Nat.mul_comm v,←Nat.two_pow_add_eq_or_of_lt ha v,Nat.add_comm]

theorem joined_acc (G d j : Nat) :
    joined d j (BitVec.ofNat 64 (acc64 G d j)) (BitVec.ofNat 64 (G/2^(d*j)%2^d))=
      BitVec.ofNat 64 (G%2^(d*(j+1))/2^(64*(d*j/64))) := by
  rw [joined_nat _ _ _ _ (acc64_lt G d j),add64]

theorem joined_flush {G d j : Nat} (h : 64≤d*j%64+d) :
    joined d j (BitVec.ofNat 64 (acc64 G d j)) (BitVec.ofNat 64 (G/2^(d*j)%2^d))=
      BitVec.ofNat 64 (G/2^(64*(d*j/64))) := by
  rw [joined_acc]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  exact VG.Proof.MlKem.mod_pow_div_mod G (by rw [Nat.mul_succ]; omega)

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackCarry.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64

theorem digit_tail (G a d c : Nat) :
    (G/2^a%2^d)/2^c=G%2^(a+d)/2^(a+c) := by
  rw [Nat.pow_add 2 a c,←Nat.div_div_eq_div_mul,Nat.pow_add 2 a d,Nat.mod_mul_right_div_self]

theorem digit_lt64 (G d j : Nat) (hd : d≤20) : G/2^(d*j)%2^d<2^64 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem acc64_lt64 (G d j : Nat) : acc64 G d j<2^64 :=
  Nat.lt_of_lt_of_le (acc64_lt G d j)
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem fieldAcc_next (G d j : Nat) (hd : d≤20) (hn : d*(j+1)%64≠0) :
    fieldAcc d j (BitVec.ofNat 64 (acc64 G d j)) (BitVec.ofNat 64 (G/2^(d*j)%2^d))=
      BitVec.ofNat 64 (acc64 G d (j+1)) := by
  have ha : d*(j+1)=d*j+d := Nat.mul_succ _ _
  by_cases hc : 64<d*j%64+d
  · rw [fieldAcc,ite_eq_left hc]
    have hb : 64*(d*(j+1)/64)=d*j+(64-d*j%64) := by rw [ha]; omega
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (digit_lt64 G d j hd),BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (acc64_lt64 G d (j+1))]
    rw [digit_tail,acc64,hb,ha]
  · rw [fieldAcc,ite_eq_right hc,joined_acc]
    have hb : d*(j+1)/64=d*j/64 := by rw [ha] at hn ⊢; omega
    rw [acc64,hb]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackStreamMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Proof.MlDsa.Pack

def byteOf (G j : Nat) : Byte := BitVec.ofNat 8 (G/2^(8*j))

theorem word_byte (G k : Nat) {j : Nat} (hj : j<8) :
    (BitVec.ofNat 64 (G/2^(8*k))).extractLsb' (8*j) 8=byteOf G (k+j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow,
    VG.Proof.MlKem.mod_pow_div_mod _ (by omega),Nat.div_div_eq_div_mul,←Nat.pow_add,←Nat.mul_add]
  rfl

theorem joined_congr (d j : Nat) (a b v : BitVec 64) (h : d*j%64≠0 → a=b) :
    joined d j a v=joined d j b v := by
  by_cases hz : d*j%64=0
  · simp only [joined,hz,↓reduceIte]
  · rw [h hz]

theorem fieldAcc_congr (d j : Nat) (a b v : BitVec 64) (h : d*j%64≠0 → a=b) :
    fieldAcc d j a v=fieldAcc d j b v := by
  unfold fieldAcc
  rw [joined_congr d j a b v h]

theorem fields_written (G d : Nat) (hd : d≤20) (m : Mem) (out : Addr) (a : BitVec 64)
    {n : Nat} (hn : n≤8) :
    let f := fieldsRun d out (fun j=>BitVec.ofNat 64 (G/2^(d*j)%2^d)) ⟨m,a⟩ n
    Written m f.mem out (8*(d*n/64)) (byteOf G) ∧
      (d*n%64≠0 → f.acc=BitVec.ofNat 64 (acc64 G d n)) := by
  induction n with
  | zero =>
    simpa only [fieldsRun,Nat.mul_zero,Nat.zero_div,Nat.zero_mod,ne_eq,not_true_eq_false,false_implies,and_true] using Written.nil m out (byteOf G)
  | succ n ih =>
    obtain ⟨hw,ha⟩ := ih (by omega)
    let f := fieldsRun d out (fun j=>BitVec.ofNat 64 (G/2^(d*j)%2^d)) ⟨m,a⟩ n
    have hj : joined d n f.acc (BitVec.ofNat 64 (G/2^(d*n)%2^d))=
        joined d n (BitVec.ofNat 64 (acc64 G d n)) (BitVec.ofNat 64 (G/2^(d*n)%2^d)) :=
      joined_congr d n _ _ _ ha
    constructor
    · by_cases hf : 64≤d*n%64+d
      · have hb : 8*(d*(n+1)/64)=8*(d*n/64)+8 := by rw [Nat.mul_succ]; omega
        change Written m (fieldMem d n f.mem out f.acc _) out _ _
        rw [fieldMem,ite_eq_left hf,hj,joined_flush hf,hb,
          show 64*(d*n/64)=8*(8*(d*n/64)) by omega]
        apply written_append hw ?_ (by have := Nat.mul_le_mul hd (show n≤8 by omega); omega)
        simpa only [Nat.mul_comm] using (written_word f.mem (out+BitVec.ofNat 64 (d*n/64*8)) 8
          (BitVec.ofNat 64 (G/2^(8*(8*(d*n/64)))))).congr (fun j hj=>word_byte G _ hj)
      · have hb : d*(n+1)/64=d*n/64 := by rw [Nat.mul_succ]; omega
        change Written m (fieldMem d n f.mem out f.acc _) out _ _
        rw [fieldMem,ite_eq_right hf,hb]
        exact hw
    · intro hnext
      change fieldAcc d n f.acc _= _
      rw [fieldAcc_congr d n f.acc (BitVec.ofNat 64 (acc64 G d n)) _ ha]
      exact fieldAcc_next G d n hd hnext

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end
