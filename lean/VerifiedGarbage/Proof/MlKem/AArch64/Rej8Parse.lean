module
public import VerifiedGarbage.Impl.MlKem.AArch64.Rej8
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Packed twelve-bit candidate decoding for ML-KEM's vector sampler -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.Ntt16

/-- The two bytes of each of eight twelve-bit candidates: bytes `3k, 3k+1`
for candidate `2k` and `3k+1, 3k+2` for candidate `2k+1`. This is the exact
table installed by the parser. -/
def gatherIndex : BitVec 128 := 0x0b0a0a09080707060504040302010100

/-- The byte of the packed stream that byte `e` of the gathered vector holds. -/
def gatherSrc (e : Nat) : Nat := 3*(e/4) + (e%4+1)/2

theorem gatherIndex_byte {e : Nat} (he : e<16) : (vbyte gatherIndex e).toNat = gatherSrc e := by
  have h : ∀ e<16, (vbyte gatherIndex e).toNat = gatherSrc e := by decide +kernel
  exact h e he

def gatherValue (x : BitVec 128) : BitVec 128 :=
  ofVBytes fun e =>
    let i := (vbyte gatherIndex e).toNat
    if i<16 then vbyte x i else 0

/-- The vector table lookup reads the two bytes of each candidate. -/
theorem gather_byte (m : Mem) (p : Addr) {e : Nat} (he : e<16) :
    vbyte (gatherValue (m.read p 16)) e = m (p+BitVec.ofNat 64 (gatherSrc e)) := by
  rw [gatherValue,vbyte_ofVBytes _ he,gatherIndex_byte he]
  have hs : gatherSrc e < 16 := by simp only [gatherSrc]; omega
  rw [ite_eq_left hs]
  exact Mem.extractLsb'_read m p hs

/-- Low twelve bits of each packed word: of each even halfword. -/
def lowMask : BitVec 128 := 0x00000fff00000fff00000fff00000fff

/-- Each halfword shifted right by four. -/
def shift4 (x : BitVec 128) : BitVec 128 := ofVHalves fun e => vhalf x e >>> 4

def parsed (x : BitVec 128) : BitVec 128 :=
  let g := gatherValue x
  VSelOp.eval .bif g (shift4 g) lowMask

theorem vhalf_and (x y : BitVec 128) (e : Nat) :
    vhalf (x &&& y) e = vhalf x e &&& vhalf y e := by
  simp only [vhalf, BitVec.extractLsb'_and]

theorem bif_half_even (a : BitVec 16) : a ^^^ ((a ^^^ a >>> 4) &&& ~~~4095) = a &&& 4095 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have k : (4095 : BitVec 16).getLsbD i = decide (i<12) := by
    have finite : ∀ j<16, (4095 : BitVec 16).getLsbD j = decide (j<12) := by decide +kernel
    exact finite i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ushiftRight, k, hi,
    decide_true, Bool.true_and]
  by_cases h : i<12
  · simp [h]
  · have : a.getLsbD (4+i) = false := BitVec.getLsbD_of_ge a _ (by omega)
    simp [h, this]

theorem bif_half_odd (a : BitVec 16) : a ^^^ ((a ^^^ a >>> 4) &&& ~~~(0 : BitVec 16)) = a >>> 4 := by
  rw [show ~~~(0 : BitVec 16) = BitVec.allOnes 16 by decide, BitVec.and_allOnes, ← BitVec.xor_assoc,
    BitVec.xor_self, BitVec.zero_xor]

theorem vhalf_xor (x y : BitVec 128) (e : Nat) :
    vhalf (x ^^^ y) e = vhalf x e ^^^ vhalf y e := by
  simp only [vhalf, BitVec.extractLsb'_xor]

theorem vhalf_not (x : BitVec 128) {e : Nat} (he : e < 8) :
    vhalf (~~~x) e = ~~~vhalf x e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vhalf, BitVec.getLsbD_extractLsb', BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
    show 16*e+i<128 by omega]

theorem parsed_lane (x : BitVec 128) {e : Nat} (he : e < 8) :
    vhalf (parsed x) e =
      if e % 2 = 0 then vhalf (gatherValue x) e &&& 4095 else vhalf (gatherValue x) e >>> 4 := by
  have hm : vhalf lowMask e = if e % 2 = 0 then 4095 else 0 := by
    have finite : ∀ j < 8, vhalf lowMask j = if j % 2 = 0 then 4095 else 0 := by decide +kernel
    exact finite e he
  simp only [parsed, VSelOp.eval]
  rw [vhalf_xor, vhalf_and, vhalf_xor, vhalf_not _ he, hm, shift4, vhalf_ofVHalves _ he]
  split
  · exact bif_half_even _
  · exact bif_half_odd _

/-- Eight consecutive twelve-bit values, before rejection. -/
def candidate (m : Mem) (p : Addr) (e : Nat) : BitVec 16 :=
  ((m.read (p + BitVec.ofNat 64 (3*(e/2))) 3).extractLsb' (12*(e%2)) 12).setWidth 16

theorem candidate_lt (m : Mem) (p : Addr) (e : Nat) : (candidate m p e).toNat < 4096 := by
  simp only [candidate, BitVec.toNat_setWidth]
  have := ((m.read (p + BitVec.ofNat 64 (3*(e/2))) 3).extractLsb' (12*(e%2)) 12).isLt
  omega

theorem parsed_candidate (m : Mem) (p : Addr) {e : Nat} (he : e < 8) :
    vhalf (parsed (m.read p 16)) e = candidate m p e := by
  rw [parsed_lane _ he]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hg : ∀ j < 16, (vhalf (gatherValue (m.read p 16)) e).getLsbD j =
      (m (p + BitVec.ofNat 64 (gatherSrc (2*e + j/8)))).getLsbD (j%8) := fun j hj => by
    rw [getLsbD_vhalf _ _ hj, ← gather_byte m p (e := 2*e + j/8) (by omega)]
    simp only [vbyte, BitVec.getLsbD_extractLsb', show j%8 < 8 by omega, decide_true, Bool.true_and]
    congr 1; omega
  have hc : (candidate m p e).getLsbD i = (decide (i < 12) &&
      (m (p + BitVec.ofNat 64 (3*(e/2) + (12*(e%2)+i)/8))).getLsbD ((12*(e%2)+i)%8)) := by
    simp only [candidate, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    by_cases h : i < 12
    · simp only [h, decide_true, Bool.true_and]
      rw [getLsbD_read m 3 _ _ (by omega), Offset.add_add]
    · simp [h]
  rw [hc]
  by_cases hp : e%2=0
  · rw [ite_eq_left hp, BitVec.getLsbD_and, hg i hi]
    have k : (4095 : BitVec 16).getLsbD i = decide (i<12) := by
      have finite : ∀ j<16, (4095 : BitVec 16).getLsbD j = decide (j<12) := by decide +kernel
      exact finite i hi
    rw [k, Bool.and_comm, hp]
    have : gatherSrc (2*e + i/8) = 3*(e/2) + (12*0+i)/8 := by simp only [gatherSrc]; omega
    by_cases h : i < 12
    · rw [this, show (12*0+i)%8 = i%8 by omega]
    · simp [h]
  · rw [ite_eq_right hp, BitVec.getLsbD_ushiftRight]
    have ho : e%2=1 := by omega
    rw [ho]
    by_cases h : i < 12
    · rw [hg (4+i) (by omega)]
      have : gatherSrc (2*e + (4+i)/8) = 3*(e/2) + (12*1+i)/8 := by simp only [gatherSrc]; omega
      rw [this, show (4+i)%8 = (12*1+i)%8 by omega]
      simp [h]
    · rw [BitVec.getLsbD_of_ge _ (4+i) (by omega)]
      simp [h]

/-- One symbolic execution for the four-instruction parsing shape. -/
theorem parse_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x2) 16)
    (hi : s.v .v16 = gatherIndex) (hm : s.v .v17 = lowMask) :
    WP isa (.block Impl.MlKem.AArch64.Rej8.parse) s fun t =>
      VChg [.v0,.v1] s t ∧ t.v .v0 = parsed (s.mem.read (s.gpr .x2) 16) := by
  refine wp_ldrq (a := s.gpr .x2) (by decide) (ptr_zero _) hr fun a ha =>
    wp_vop (d := .v0) rfl fun b hb =>
    wp_vop (d := .v1) rfl fun c hc =>
    wp_vop (d := .v0) rfl fun t ht => wp_nil ?_
  refine ⟨(((ha.chg.trans hb.chg).trans hc.chg).trans ht.chg).mono (by decide), ?_⟩
  rw [ht.v, hc.get .v0, hc.v, hc.get .v17, hb.get .v17, ha.get .v17, hm, hb.v,
    ha.get .v16, hi, ha.v]
  rfl

end VG.Proof.MlKem.AArch64.Rej8
