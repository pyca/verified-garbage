import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed66
import VerifiedGarbage.Proof.MlKem.Mem

/-! ## From `ResidentLast.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_ldrb wp_lsl wp_add)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (seedLast)

def lastWord (m : Mem) (p : Addr) : BitVec 64 :=
  (m (p+64)).setWidth 64 + ((m (p+65)).setWidth 64 <<< 8)

/-- Read exactly the final two seed bytes into the low 16 bits of a scalar word. -/
theorem seedLast_ok {s : State} {r n : Reg} {a : Addr} (hr8 : r ≠ .x8)
    (hnr : n ≠ r) (ha : s.gpr n = a)
    (hin64 : InRegions (s.rd++s.wr) (a+64) 1)
    (hin65 : InRegions (s.rd++s.wr) (a+65) 1) :
    WP isa (.block (seedLast r n)) s fun t => Only [r,.x8] s t ∧ t.gpr r = lastWord s.mem a := by
  unfold seedLast
  refine wp_ldrb (a := a+64) (by decide) (by rw [ha]; rfl) hin64 fun s1 h1 e1 => ?_
  refine wp_ldrb (a := a+65) (by decide) (by rw [h1.get n (by simpa using hnr),ha]; rfl)
    (by rw [h1.rd,h1.wr]; exact hin65) fun s2 h2 e2 => ?_
  refine wp_lsl (by decide) fun s3 h3 e3 => wp_add fun t h4 e4 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact (((h1.trans h2).trans h3).trans h4).mono (by simp)
  · rw [e4,e3,h3.get r (by simpa using hr8),h2.get r (by simpa using hr8),e1,e2,h1.mem]
    rfl
end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentSeed.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (toNat_lsl_n toNat_add_n)

def tailWord (m : Mem) (p : Addr) : BitVec 64 := lastWord m p + 0x1f0000

theorem toNat_append_add {n k : Nat} (a : BitVec n) (b : BitVec k) :
    (a++b).toNat = a.toNat * 2^k + b.toNat := by
  rw [BitVec.toNat_append,← Nat.shiftLeft_add_eq_or_of_lt b.isLt,Nat.shiftLeft_eq]

theorem tailWord_eq (m : Mem) (p : Addr) :
    tailWord m p = (((0#40 ++ 0x1f#8) ++ m (p+65)) ++ m (p+64)) := by
  have h0 := (m (p+64)).isLt
  have h1 := (m (p+65)).isLt
  have hs : (((m (p+65)).setWidth 64) <<< 8).toNat = (m (p+65)).toNat * 256 := by
    rw [toNat_lsl_n (by rw [BitVec.toNat_setWidth]; omega),BitVec.toNat_setWidth]
    omega
  apply BitVec.eq_of_toNat_eq
  unfold tailWord lastWord
  rw [toNat_add_n (by rw [BitVec.toNat_add,BitVec.toNat_setWidth,hs]; change (_ % _ + 2031616 < _); omega),
    toNat_add_n (by rw [BitVec.toNat_setWidth,hs]; omega),BitVec.toNat_setWidth,hs]
  simp only [toNat_append_add,BitVec.toNat_ofNat]
  rw [show (0x1f0000 : BitVec 64).toNat = 2031616 from rfl]
  simp only [Nat.reducePow,Nat.zero_mod,Nat.reduceMod,Nat.reduceMul,Nat.reduceAdd]
  omega

theorem tailWord_byte (m : Mem) (p : Addr) {k : Nat} (hk : k < 8) :
    (tailWord m p).extractLsb' (8*k) 8 =
      if k = 0 then m (p+64) else if k = 1 then m (p+65) else if k = 2 then 0x1f else 0 := by
  rw [tailWord_eq]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with h | h | h | h
  · subst k
    simp only [Nat.mul_zero,BitVec.extractLsb'_append_eq_right,ite_true]
  · subst k
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    simp only [Nat.reduceMul,Nat.reduceSub,BitVec.extractLsb'_append_eq_right,
      ite_eq_right (by decide : ¬ (1:Nat) = 0),ite_true]
  · subst k
    rw [BitVec.extractLsb'_append_eq_of_le (by decide),BitVec.extractLsb'_append_eq_of_le (by decide)]
    simp only [Nat.reduceMul,Nat.reduceSub,BitVec.extractLsb'_append_eq_right,
      ite_eq_right (by decide : ¬ (2:Nat) = 0),ite_eq_right (by decide : ¬ (2:Nat) = 1),ite_true]
    rfl
  · rw [BitVec.extractLsb'_append_eq_of_le (by omega),BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega)]
    simp only [ite_eq_right (by omega : ¬ k = 0),ite_eq_right (by omega : ¬ k = 1),
      ite_eq_right (by omega : ¬ k = 2)]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp

/-- The initial state obtained by absorbing a 66-byte seed and SHAKE padding. -/
def seedState (m : Mem) (p : Addr) : Spec.Sha3.State := Vector.ofFn fun i : Fin 25 =>
  if i.val < 8 then m.readW (p+BitVec.ofNat 64 (8*i.val)) 64
  else if i.val = 8 then tailWord m p
  else if i.val = 16 then 0x8000000000000000 else 0

theorem pad_byte : ∀ k < 8, (0x8000000000000000 : BitVec 64).extractLsb' (8*k) 8 =
    if k = 7 then 0x80 else 0 := by decide

theorem seedState_get (m : Mem) (p : Addr) {i : Nat} (hi : i < 25) :
    (seedState m p)[i]! = if i < 8 then m.readW (p+BitVec.ofNat 64 (8*i)) 64
      else if i = 8 then tailWord m p else if i = 16 then 0x8000000000000000 else 0 := by
  rw [Proof.Sha3.getElem!_eq _ hi]
  unfold seedState
  rw [Vector.getElem_ofFn]

theorem seedState_eq (m : Mem) (p : Addr) :
    seedState m p = Proof.MlDsa.AArch64.Optimized.ResidentSeed66.A0 (Spec.Sha3.bytesAt m p 66) := by
  apply Proof.Sha3.ext_bytes
  intro j hj
  rw [Proof.MlDsa.AArch64.Optimized.ResidentSeed66.byteOf_A0 (Proof.Sha3.bytesAt_length _ _ _) hj]
  unfold Proof.Sha3.byteOf
  rw [seedState_get m p (by omega)]
  by_cases h32 : j < 64
  · rw [ite_eq_left (by omega : j/8 < 8),ite_eq_left (by omega : j < 66),
      Proof.MlKem.bytesAt_getD m p (by omega)]
    change (m.read (p+BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _
    rw [Mem.extractLsb'_read m _ (by omega),BitVec.add_assoc,← BitVec.ofNat_add,
      show 8*(j/8)+j%8 = j by omega]
  · rw [ite_eq_right (by omega : ¬ j/8 < 8)]
    by_cases h40 : j < 72
    · rw [ite_eq_left (by omega : j/8 = 8),tailWord_byte m p (by omega)]
      rcases (show j = 64 ∨ j = 65 ∨ j = 66 ∨ 67 ≤ j by omega) with h | h | h | h
      · subst j
        simp only [Nat.reduceMod,ite_true]
        rw [Proof.MlKem.bytesAt_getD m p (by decide)]
        rfl
      · subst j
        simp only [Nat.reduceMod,ite_eq_right (by decide : ¬ (1:Nat) = 0),ite_true]
        rw [Proof.MlKem.bytesAt_getD m p (by decide)]
        rfl
      · subst j
        simp
      · simp (disch := omega) only [ite_eq_right]
    · rw [ite_eq_right (by omega : ¬ j/8 = 8)]
      by_cases h20 : j/8 = 16
      · rw [ite_eq_left h20,pad_byte (j%8) (by omega)]
        by_cases he : j = 135 <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
      · rw [ite_eq_right h20]
        simp (disch := omega) only [ite_eq_right]
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp
end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end
