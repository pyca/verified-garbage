import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackCarry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFields
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten

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
