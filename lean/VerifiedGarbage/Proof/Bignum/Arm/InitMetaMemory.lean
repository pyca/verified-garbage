module

public import VerifiedGarbage.Proof.Bignum.Arm.InitMeta
public import VerifiedGarbage.Proof.Bignum.Arm.RoundMeta

/-! # Metadata stores establish the first round and preserve other workspace bytes -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

theorem initMeta_header (s : State) {base : BitVec 32} {size tmp a b mod acc out n : Nat} {inv : BitVec 32}
    (nowrap : base.toNat + size ≤ 2 ^ 32) (fit : tmp + 32 ≤ size)
    (count : s.gpr .r7 = BitVec.ofNat 32 n)
    (pa : s.gpr .r8 = base + BitVec.ofNat 32 a) (pb : s.gpr .r9 = base + BitVec.ofNat 32 b)
    (pm : s.gpr .r11 = base + BitVec.ofNat 32 mod) (pi : s.gpr .r12 = inv)
    (po : s.gpr .r10 = base + BitVec.ofNat 32 out) (pc : s.gpr .r6 = base + BitVec.ofNat 32 acc) :
    RoundMeta (initMetaMem s (State.addr base) tmp) base tmp a b mod acc n 0 inv ∧
    (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 24)) 32 =
      base + BitVec.ofNat 32 out := by
  have hb : (State.addr base).toNat + size ≤ 2 ^ 32 := by
    rw [VG.Proof.X25519.Arm.addr_toNat]; exact nowrap
  have h0 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 0)) 32 = s.gpr .r7 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 0) = _
    unfold initMetaMem
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_self]
  have h1 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 4)) 32 = s.gpr .r9 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 4) = _
    unfold initMetaMem
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_self]
  have h2 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 8)) 32 = s.gpr .r11 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 8) = _
    unfold initMetaMem
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_self]
  have h3 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 12)) 32 = s.gpr .r12 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 12) = _
    unfold initMetaMem
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_self]
  have h4 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 16)) 32 = s.gpr .r8 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 16) = _
    unfold initMetaMem
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_self]
  have h5 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 20)) 32 = s.gpr .r7 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 20) = _
    unfold initMetaMem
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_self]
  have h6 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 24)) 32 = s.gpr .r10 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 24) = _
    unfold initMetaMem
    rw [w32_write_ne hb (by omega) (by omega) (by omega)]
    rw [w32_write_self]
  have h7 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 28)) 32 = s.gpr .r6 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 28) = _
    unfold initMetaMem
    rw [w32_write_self]
  refine ⟨⟨h0.trans count, h1.trans pb, h2.trans pm, h3.trans pi, ?_, ?_, h7.trans pc⟩, h6.trans po⟩
  · simpa only [Nat.mul_zero, Nat.add_zero] using h4.trans pa
  · simpa only [Nat.sub_zero] using h5.trans count

theorem initMeta_outside (s : State) {base : Addr} {tmp : Nat} (fit : tmp + 32 ≤ 2 ^ 64) :
    Outside base tmp 32 s.mem (initMetaMem s base tmp) := by
  let m0 := s.mem
  let m1 := m0.writeW (off base (tmp + 0)) (s.gpr .r7)
  have h0 : Outside base tmp 32 m0 m1 :=
    (writeW32_outside m0 base (d := tmp + 0) (s.gpr .r7) (by omega)).mono
      (by omega) (by omega)
  let m2 := m1.writeW (off base (tmp + 4)) (s.gpr .r9)
  have h1 : Outside base tmp 32 m1 m2 :=
    (writeW32_outside m1 base (d := tmp + 4) (s.gpr .r9) (by omega)).mono
      (by omega) (by omega)
  let m3 := m2.writeW (off base (tmp + 8)) (s.gpr .r11)
  have h2 : Outside base tmp 32 m2 m3 :=
    (writeW32_outside m2 base (d := tmp + 8) (s.gpr .r11) (by omega)).mono
      (by omega) (by omega)
  let m4 := m3.writeW (off base (tmp + 12)) (s.gpr .r12)
  have h3 : Outside base tmp 32 m3 m4 :=
    (writeW32_outside m3 base (d := tmp + 12) (s.gpr .r12) (by omega)).mono
      (by omega) (by omega)
  let m5 := m4.writeW (off base (tmp + 16)) (s.gpr .r8)
  have h4 : Outside base tmp 32 m4 m5 :=
    (writeW32_outside m4 base (d := tmp + 16) (s.gpr .r8) (by omega)).mono
      (by omega) (by omega)
  let m6 := m5.writeW (off base (tmp + 20)) (s.gpr .r7)
  have h5 : Outside base tmp 32 m5 m6 :=
    (writeW32_outside m5 base (d := tmp + 20) (s.gpr .r7) (by omega)).mono
      (by omega) (by omega)
  let m7 := m6.writeW (off base (tmp + 24)) (s.gpr .r10)
  have h6 : Outside base tmp 32 m6 m7 :=
    (writeW32_outside m6 base (d := tmp + 24) (s.gpr .r10) (by omega)).mono
      (by omega) (by omega)
  let m8 := m7.writeW (off base (tmp + 28)) (s.gpr .r6)
  have h7 : Outside base tmp 32 m7 m8 :=
    (writeW32_outside m7 base (d := tmp + 28) (s.gpr .r6) (by omega)).mono
      (by omega) (by omega)
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7)))))))

end VG.Proof.Bignum.Arm
