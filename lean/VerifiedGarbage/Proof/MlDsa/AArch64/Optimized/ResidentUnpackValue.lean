import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackArithmetic

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask

/-- Constants consumed by the arithmetic part of each four-field group. -/
structure ParseConstants (d : Nat) (s : State) : Prop where
  powers : ∀ e<4, vword (s.v .v23) e=BitVec.ofNat 32 (2^((if d=20 then 4 else 6)-d*e%8))
  mask : ∀ e<4, vword (s.v .v22) e=BitVec.ofNat 32 (2^d-1)
  bound : ∀ e<4, vword (s.v .v21) e=BitVec.ofNat 32 (2^(d-1))
  modulus : ∀ e<4, vword (s.v .v20) e=8380417#32

def fieldValue (m : Mem) (a : Addr) (d i : Nat) : Nat :=
  (((m.read (a+BitVec.ofNat 64 (d*i/8)) 3).setWidth 32).extractLsb' (d*i%8) d).toNat

/-- The composed TBL, alignment and signed correction computes precisely the
canonical representative of gamma minus the packed little-endian field. -/
theorem parsed_word {s : State} {m : Mem} {a : Addr} {d g e : Nat}
    (hd : d=18 ∨ d=20) (hg : g<4) (he : e<4) (hc : ParseConstants d s)
    (h0 : s.v .v0=m.read a 16) (h1 : s.v .v1=m.read (a+BitVec.ofNat 64 16) 16)
    (h2 : s.v .v2=m.read (a+BitVec.ofNat 64 (2*d-16)) 16) :
    (vword (correctVec (alignVec (gatherValue s.v d g) (s.v .v23) (s.v .v22)
      (if d=20 then 4 else 6)) (s.v .v21) (s.v .v20)) e).toNat =
      (2^(d-1)+8380417-fieldValue m a d (4*g+e))%8380417 := by
  rw [correctVec_word _ _ _ he (hc.modulus e he),
    alignVec_word _ _ _ hd he (hc.powers e he) (hc.mask e he),hc.bound e he,
    gather_word hd hg he h0 h1 h2]
  have hd32 : d≤32 := by omega
  have hb : (BitVec.ofNat 32 (2^(d-1))).toNat<8380417 := by
    rcases hd with rfl | rfl <;> decide
  have hx : (BitVec.setWidth 32
      (((m.read (a+BitVec.ofNat 64 (d*(4*g+e)/8)) 3).setWidth 32).extractLsb' (d*e%8) d)).toNat<8380417 := by
    rw [BitVec.toNat_setWidth_of_le hd32]
    have h := (((m.read (a+BitVec.ofNat 64 (d*(4*g+e)/8)) 3).setWidth 32).extractLsb' (d*e%8) d).isLt
    rcases hd with rfl | rfl <;> omega
  rw [unpackWord_toNat hb hx,BitVec.toNat_setWidth_of_le hd32]
  have hp : (BitVec.ofNat 32 (2^(d-1))).toNat=2^(d-1) := by
    rcases hd with rfl | rfl <;> decide
  simp only [hp,fieldValue,(fieldShift_bounds (g := g) (e := e) hd).1]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
