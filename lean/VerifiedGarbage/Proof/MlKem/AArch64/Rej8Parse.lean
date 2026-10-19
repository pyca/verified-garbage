module
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.MlKem.AArch64.Rej8
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem

/-! # Packed twelve-bit candidate decoding for ML-KEM's vector sampler -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.Ntt16

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

/-- Low twelve bits of each packed word. -/
def lowMask : BitVec 128 := 0x00000fff00000fff00000fff00000fff

def shift12 (x : BitVec 128) : BitVec 128 :=
  ofVWords (vword x 0 >>> 12) (vword x 1 >>> 12)
    (vword x 2 >>> 12) (vword x 3 >>> 12)

def parsed (x : BitVec 128) : BitVec 128 :=
  let g := gatherValue x
  let low := g &&& lowMask
  let high := shift12 g
  VPermOp.eval .zip1 .h8 (VPermOp.eval .uzp1 .h8 low low)
    (VPermOp.eval .uzp1 .h8 high high)


theorem vword_shift12 (x : BitVec 128) {e : Nat} (he : e < 4) :
    vword (shift12 x) e = vword x e >>> 12 := by
  rw [shift12, vword_ofVWords _ _ _ _ he]
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl

theorem vhalf_and (x y : BitVec 128) (e : Nat) :
    vhalf (x &&& y) e = vhalf x e &&& vhalf y e := by
  simp only [vhalf, BitVec.extractLsb'_and]

theorem parsed_lane (x : BitVec 128) {e : Nat} (he : e < 8) :
    vhalf (parsed x) e =
      if e % 2 = 0 then (vword (gatherValue x) (e/2)).extractLsb' 0 16 &&& 4095
      else (vword (gatherValue x) (e/2) >>> 12).extractLsb' 0 16 := by
  rw [parsed, vhalf_perm_h8 _ _ _ he]
  simp only
  have h2 : e/2 < 8 := by omega
  have h4 : e/2 < 4 := by omega
  have hm : vhalf lowMask (2*(e/2)) = 4095 := by
    have finite : ∀ j < 4, vhalf lowMask (2*j) = 4095 := by decide +kernel
    exact finite _ h4
  split
  · rw [vhalf_perm_h8 _ _ _ h2]
    simp only [ite_eq_left h4]
    rw [vhalf_and, hm, ← vword_lo]
  · rw [vhalf_perm_h8 _ _ _ h2]
    simp only [ite_eq_left h4]
    rw [← vword_lo, vword_shift12 _ h4]

/-- Eight consecutive twelve-bit values, before rejection. -/
def candidate (m : Mem) (p : Addr) (e : Nat) : BitVec 16 :=
  ((m.read (p + BitVec.ofNat 64 (3*(e/2))) 3).extractLsb' (12*(e%2)) 12).setWidth 16

theorem candidate_lt (m : Mem) (p : Addr) (e : Nat) : (candidate m p e).toNat < 4096 := by
  simp only [candidate, BitVec.toNat_setWidth]
  have := ((m.read (p + BitVec.ofNat 64 (3*(e/2))) 3).extractLsb' (12*(e%2)) 12).isLt
  omega

theorem parsed_candidate (m : Mem) (p : Addr) {e : Nat} (he : e < 8) :
    vhalf (parsed (m.read p 16)) e = candidate m p e := by
  rw [parsed_lane _ he, gather_word m p (by omega)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hp : e%2=0
  · rw [ite_eq_left hp]
    simp only [candidate, hp, Nat.mul_zero, BitVec.getLsbD_and,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, Nat.zero_add,
      hi, decide_true, Bool.true_and]
    have mask : (4095 : BitVec 16).getLsbD i = decide (i<12) := by
      have finite : ∀ j<16, (4095 : BitVec 16).getLsbD j = decide (j<12) := by decide +kernel
      exact finite i hi
    rw [mask]
    simp only [show i<32 by omega, decide_true, Bool.true_and]
    exact Bool.and_comm _ _
  · rw [ite_eq_right hp]
    have ho : e%2=1 := by omega
    simp only [candidate, ho, Nat.mul_one, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, Nat.zero_add,
      hi, decide_true, Bool.true_and]
    by_cases hl : i<12
    · simp [hl, show i+12<32 by omega, Nat.add_comm]
    · rw [BitVec.getLsbD_of_ge (m.read (p + BitVec.ofNat 64 (3*(e/2))) 3) (12+i) (by omega)]
      simp [hl]

/-- One symbolic execution for the seven-instruction parsing shape. -/
theorem parse_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x2) 16)
    (hi : s.v .v16 = gatherIndex) (hm : s.v .v17 = lowMask) :
    WP isa (.block Impl.MlKem.AArch64.Rej8.parse) s fun t =>
      VChg [.v0,.v1] s t ∧ t.v .v0 = parsed (s.mem.read (s.gpr .x2) 16) := by
  refine wp_ldrq (a := s.gpr .x2) (by decide) (ptr_zero _) hr fun a ha =>
    wp_vop (d := .v0) rfl fun b hb =>
    wp_vop (d := .v1) rfl fun c hc =>
    wp_vop (d := .v0) rfl fun d hd =>
    wp_vop (d := .v0) rfl fun e he =>
    wp_vop (d := .v1) rfl fun f hf =>
    wp_vop (d := .v0) rfl fun t ht => wp_nil ?_
  refine ⟨((((((ha.chg.trans hb.chg).trans hc.chg).trans hd.chg).trans he.chg).trans
    hf.chg).trans ht.chg).mono (by decide), ?_⟩
  rw [ht.v, hf.get .v0, he.v, hd.v, hc.get .v0, hb.v,
    ha.get .v16, hi, ha.v, hc.get .v17, hb.get .v17, ha.get .v17, hm,
    hf.v, he.get .v1, hd.get .v1, hc.v, hb.v, ha.get .v16, hi, ha.v]
  rfl

end VG.Proof.MlKem.AArch64.Rej8
