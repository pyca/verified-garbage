module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeContext
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes

/-! ### `Ffdh.Arm.ParameterCandidate.ShapeFirst`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.ShapeBits`, which only this module used -/

section

/-! Native 32-bit mask construction implements the shared first-octet
shaping rule, including an exact byte boundary. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG

private theorem topMask_nat (x j : Nat) :
    x % 2 ^ (j + 1) ||| 2 ^ j = x % 2 ^ j + 2 ^ j := by
  rw [← Nat.or_two_pow_eq_add_of_lt (Nat.mod_lt x (Nat.two_pow_pos j))]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
  by_cases same : i = j
  · simp [same]
  · have cut : (i < j + 1) = (i < j) := propext (by omega_using [same])
    simp only [cut]

theorem topMask_byte (b : Byte) {j : Nat} (bound : j < 8) :
    (((b.setWidth 32 &&& BitVec.ofNat 32 (2 ^ (j + 1) - 1)) |||
      BitVec.ofNat 32 (2 ^ j)).setWidth 8) = VG.Proof.Ffdh.ParameterCandidate.topByte j b := by
  have high : 2 ^ j < 256 := Nat.pow_lt_pow_right (by decide) bound
  have full : 2 ^ (j + 1) ≤ 256 := Nat.pow_le_pow_right (n := 2) (i := j + 1) (j := 8) (by decide) (by omega_using [bound])
  have byte := b.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_and,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_using [] : b.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega_using [full] : 2 ^ (j + 1) - 1 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega_using [high] : 2 ^ j < 2 ^ 32), Nat.and_two_pow_sub_one_eq_mod,
    topMask_nat, VG.Proof.Ffdh.ParameterCandidate.topByte_value bound]
  apply Nat.mod_eq_of_lt
  have lo := Nat.mod_lt b.toNat (Nat.two_pow_pos j)
  have pow : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
  omega

theorem maskTopWord {j : Nat} (bound : j < 8) :
    (BitVec.ofNat 32 (2 ^ (j + 1) - 1) >>> 1) + 1 = BitVec.ofNat 32 (2 ^ j) := by
  have full : 2 ^ (j + 1) ≤ 256 := Nat.pow_le_pow_right (n := 2) (i := j + 1) (j := 8) (by decide) (by omega_using [bound])
  have pow : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
  have positive := Nat.two_pow_pos j
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega_using [full] : 2 ^ (j + 1) - 1 < 2 ^ 32), BitVec.toNat_ofNat]
  have half : (2 ^ (j + 1) - 1) / 2 ^ 1 + 1 = 2 ^ j := by omega_using [positive]
  rw [half]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! Apply the generated mask and high bit to the candidate's first octet. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem shapeFirst_ok (s : State) (dst : BitVec 32) {j : Nat} (bound : j < 8)
    (slotRead : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 4)) 4)
    (slot : s.mem.readW (State.addr (s.sp + 4)) 32 = dst)
    (read : InRegions (s.rd ++ s.wr) (State.addr dst) 1)
    (write : InRegions s.wr (State.addr dst) 1)
    (mask : s.gpr .r7 = BitVec.ofNat 32 (2 ^ (j + 1) - 1)) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeFirst) s fun t =>
      (t.gpr .r4 = dst ∧ t.mem = s.mem.writeW (State.addr dst)
        (VG.Proof.Ffdh.ParameterCandidate.topByte j (s.mem (State.addr dst)))) ∧
        Rest [.r3, .r4, .r9] s t := by
  refine withRest_all [.r3, .r4, .r9] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.shapeFirst
  ffrun [show (4#32) = (4 : BitVec 32) from rfl, BitVec.add_zero,
    slotRead, slot, read, write, mask, maskTopWord bound, topMask_byte _ bound]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! First-octet shaping preserves all other copied bytes and saved arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

theorem shapeTop_ok (s : State) {dst src : BitVec 32} {bs : List Byte} {bits j : Nat}
    (h : ShapeContext dst src bs bits s) (bound : j < 8)
    (copied : ∀ i < bs.length, s.mem (State.addr (dst + BitVec.ofNat 32 i)) = bs[i]?.getD 0)
    (mask : s.gpr .r7 = BitVec.ofNat 32 (2 ^ (j + 1) - 1)) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeFirst) s fun t =>
      ShapeContext dst src bs bits t ∧ t.gpr .r4 = dst ∧
      (∀ i < bs.length, t.mem (State.addr (dst + BitVec.ofNat 32 i)) =
        (VG.Proof.Ffdh.ParameterCandidate.topCut bs j).getD i 0) ∧
      Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem ∧ Rest [.r3, .r4, .r9] s t := by
  have positive : 0 < bs.length := by have := h.size; omega_using [this]
  have read := h.readByte (i := 0) positive
  have write := h.writeByte (i := 0) positive
  simp only [BitVec.add_zero] at read write
  refine WP.mono (shapeFirst_ok s dst bound (h.frame.read (d := 4) (by decide))
    (h.frame.saved 4 (by decide)) read write mask) ?_
  rintro t ⟨⟨ptr, mem⟩, rest⟩
  have contains := h.containsByte (i := 0) positive
  simp only [BitVec.add_zero] at contains
  have frame : Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (by simp) _ contains
  refine ⟨h.after_output frame rest, ptr, ?_, frame, rest⟩
  intro i hi
  rw [mem, VG.WriteBytes.writeW8_apply, VG.Proof.Ffdh.ParameterCandidate.topCut_getD]
  by_cases first : i = 0
  · subst i
    simp only [BitVec.add_zero, ite_true]
    have byte := copied 0 positive
    simp only [BitVec.add_zero] at byte
    rw [byte]
    rfl
  · have different : State.addr (dst + BitVec.ofNat 32 i) ≠ State.addr dst := by
      intro same
      have eq := h.copyCtx.distinct i hi 0 positive (by simpa using same)
      exact first eq
    rw [ite_eq_right different, ite_eq_right first]
    exact copied i hi

end VG.Proof.Ffdh.Arm.ParameterCandidate
