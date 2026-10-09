import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackIndex
import VerifiedGarbage.Proof.Framework.AArch64.Tbl

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask

private theorem vbyte_read (m : Mem) (a : Addr) {e : Nat} (he : e<16) :
    vbyte (m.read a 16) e=m (a+BitVec.ofNat 64 e) := Mem.extractLsb'_read m a he

/-- Byte lookup from the two full input vectors and the overlapping tail. -/
theorem tableByte_three {v : VReg → BitVec 128} {m : Mem} {a : Addr} {d : Nat}
    (hd : d=18 ∨ d=20)
    (h0 : v .v0=m.read a 16) (h1 : v .v1=m.read (a+BitVec.ofNat 64 16) 16)
    (h2 : v .v2=m.read (a+BitVec.ofNat 64 (2*d-16)) 16)
    {i : Nat} (hi : i<48) : tableByte v .v0 i=m (a+BitVec.ofNat 64 (tableOffset d i)) := by
  unfold tableByte
  by_cases h16 : i<16
  · rw [show i/16=0 by omega,show Nat.repeat VReg.succ 0 .v0=.v0 from rfl,h0,
      vbyte_read _ _ (by omega),Nat.mod_eq_of_lt h16]
    simp only [tableOffset,ite_eq_left (by omega : i<32)]
  · by_cases h32 : i<32
    · rw [show i/16=1 by omega,show Nat.repeat VReg.succ 1 .v0=.v1 from rfl,h1,
        vbyte_read _ _ (by omega),Offset.add_add]
      simp only [tableOffset,ite_eq_left h32]
      rw [show 16+i%16=i by omega]
    · rw [show i/16=2 by omega,show Nat.repeat VReg.succ 2 .v0=.v2 from rfl,h2,
        vbyte_read _ _ (by omega),Offset.add_add]
      simp only [tableOffset,ite_eq_right h32]
      rw [show 2*d-16+i%16=i+2*d-48 by rcases hd with rfl | rfl <;> omega]

/-- Mathematical index vector installed by `Unpack.init`. -/
def gatherIndex (d g : Nat) : BitVec 128 :=
  ofVBytes fun i => BitVec.ofNat 8 ((Unpack.indices d g)[i]!)

/-- Every gathered word consists of exactly three consecutive input bytes
and a zero top byte, before alignment and masking. -/
theorem gather_byte {v : VReg → BitVec 128} {m : Mem} {a : Addr} {d g e : Nat}
    (hd : d=18 ∨ d=20) (hg : g<4) (he : e<16)
    (h0 : v .v0=m.read a 16) (h1 : v .v1=m.read (a+BitVec.ofNat 64 16) 16)
    (h2 : v .v2=m.read (a+BitVec.ofNat 64 (2*d-16)) 16) :
    (let ix := (vbyte (gatherIndex d g) e).toNat
      if ix<48 then tableByte v .v0 ix else 0) =
    if e%4<3 then m (a+BitVec.ofNat 64 (d*(4*g+e/4)/8+e%4)) else 0 := by
  have hc := indexCorrect_of_width hd g hg e he
  simp only [gatherIndex,vbyte_ofVBytes _ he,BitVec.toNat_ofNat]
  by_cases hl : e%4<3
  · have hi := hc.1 hl
    rw [Nat.mod_eq_of_lt (by omega : (Unpack.indices d g)[e]!<256),ite_eq_left hi.1,
      ite_eq_left hl,tableByte_three hd h0 h1 h2 hi.1,hi.2.1]
  · have hi := hc.2 (by omega)
    rw [hi]
    simp only [ite_eq_right (by decide : ¬ (255:Nat)<48),ite_eq_right hl]

def gatherValue (v : VReg → BitVec 128) (d g : Nat) : BitVec 128 :=
  ofVBytes fun e =>
    let ix := (vbyte (gatherIndex d g) e).toNat
    if ix<48 then tableByte v .v0 ix else 0

/-- Each gathered 32-bit lane contains a zero-extended 24-bit input window. -/
theorem gather_word {v : VReg → BitVec 128} {m : Mem} {a : Addr} {d g e : Nat}
    (hd : d=18 ∨ d=20) (hg : g<4) (he : e<4)
    (h0 : v .v0=m.read a 16) (h1 : v .v1=m.read (a+BitVec.ofNat 64 16) 16)
    (h2 : v .v2=m.read (a+BitVec.ofNat 64 (2*d-16)) 16) :
    vword (gatherValue v d g) e =
      (m.read (a+BitVec.ofNat 64 (d*(4*g+e)/8)) 3).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vword,BitVec.getLsbD_extractLsb',gatherValue]
  rw [show 32*e+i=8*(4*e+i/8)+i%8 by omega,
    getLsbD_ofVBytes _ (by omega) (by omega),gather_byte hd hg (by omega) h0 h1 h2]
  simp only [show (4*e+i/8)%4=i/8 by omega,show (4*e+i/8)/4=e by omega,
    BitVec.getLsbD_setWidth]
  by_cases hl : i<24
  · rw [ite_eq_left (by omega : i/8<3),getLsbD_read m 3 _ i hl,Offset.add_add]
  · rw [ite_eq_right (by omega : ¬ i/8<3),BitVec.getLsbD_of_ge (m.read (a+BitVec.ofNat 64 (d*(4*g+e)/8)) 3) i (by omega)]
    simp [BitVec.getLsbD]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
