import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackGather

/-! ## From `ResidentRejWord.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

/-- A masked 23-bit candidate makes the high bit of its difference from q
an exact acceptance bit. No modular wraparound is mistaken for acceptance. -/
theorem candidate_bit (z : BitVec 32) (hz : z.toNat < 2^23) :
    (z - 8380417) >>> 31 = if z.toNat < 8380417 then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_sub]
  have hq : (8380417 : BitVec 32).toNat = 8380417 := rfl
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  by_cases h : z.toNat < 8380417
  · rw [ite_eq_left h]
    simp only [hq, h1, Nat.shiftRight_eq_div_pow, Nat.reducePow] at hz ⊢
    omega
  · rw [ite_eq_right h]
    simp only [hq, h0, Nat.shiftRight_eq_div_pow, Nat.reducePow] at hz ⊢
    omega

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejGather.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

/-- Four consecutive three-byte candidates, with an out-of-range index for
 each zero top byte. This is the exact table installed by the parser. -/
def gatherIndex : BitVec 128 := 0xff0b0a09ff080706ff050403ff020100

theorem gatherIndex_byte {e : Nat} (he : e<16) :
    (vbyte gatherIndex e).toNat = if e%4<3 then 3*(e/4)+e%4 else 255 := by
  have h : ∀ e<16, (vbyte gatherIndex e).toNat =
      if e%4<3 then 3*(e/4)+e%4 else 255 := by decide +kernel
  exact h e he

def gatherValue (x : BitVec 128) : BitVec 128 :=
  ofVBytes fun e =>
    let i := (vbyte gatherIndex e).toNat
    if i<16 then vbyte x i else 0

/-- The vector table lookup reads exactly the three bytes of each candidate. -/
theorem gather_byte (m : Mem) (p : Addr) {e : Nat} (he : e<16) :
    vbyte (gatherValue (m.read p 16)) e =
      if e%4<3 then m (p+BitVec.ofNat 64 (3*(e/4)+e%4)) else 0 := by
  rw [gatherValue,vbyte_ofVBytes _ he,gatherIndex_byte he]
  split
  · rw [ite_eq_left (by omega)]
    exact Mem.extractLsb'_read m p (by omega)
  · rfl

/-- Masking the top bit of each gathered word gives exactly a 23-bit read,
 independent of the byte following the candidate. -/
theorem gather_word (m : Mem) (p : Addr) {e : Nat} (he : e<4) :
    vword (gatherValue (m.read p 16)) e =
      (m.read (p+BitVec.ofNat 64 (3*e)) 3).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vword,BitVec.getLsbD_extractLsb']
  rw [show 32*e+i=8*(4*e+i/8)+i%8 by omega]
  have hb := congrArg (fun x : BitVec 8 => x.getLsbD (i%8))
    (gather_byte m p (e := 4*e+i/8) (by omega))
  simp only [vbyte,BitVec.getLsbD_extractLsb', show i%8<8 by omega,decide_true,Bool.true_and] at hb
  simp only [hi,decide_true,Bool.true_and]
  rw [hb]
  simp only [show (4*e+i/8)%4=i/8 by omega,show (4*e+i/8)/4=e by omega,
    BitVec.getLsbD_setWidth]
  by_cases hl : i<24
  · rw [ite_eq_left (by omega : i/8<3),getLsbD_read m 3 _ i hl,Offset.add_add]
    simp only [hi,decide_true,Bool.true_and]
  · rw [ite_eq_right (by omega : ¬i/8<3),
      BitVec.getLsbD_of_ge (m.read (p+BitVec.ofNat 64 (3*e)) 3) i (by omega)]
    simp [BitVec.getLsbD]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
