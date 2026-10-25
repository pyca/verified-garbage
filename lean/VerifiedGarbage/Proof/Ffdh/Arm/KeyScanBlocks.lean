module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.TCB.Arm.Isa

/-! The byte-reading and control blocks of the native public-bound scan. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldrb ofNat_beq_zero)

theorem byteZero32 : ∀ b : Byte, (b.setWidth 32 - 0#32 == 0#32) = decide (b = 0) := by decide +kernel

theorem countOne32 {n : Nat} (positive : 0 < n) (fits : n < 2 ^ 32) :
    (BitVec.ofNat 32 n - 1#32 == 0#32) = decide (n = 1) := by
  change (BitVec.ofNat 32 n - BitVec.ofNat 32 1 == (0 : BitVec 32)) = _
  rw [Offset.ofNat_sub_ofNat (by omega), ofNat_beq_zero (by omega)]
  apply decide_eq_decide.mpr
  omega

theorem scanRead_ok (s : State) {base src : BitVec 32} {len : Nat} {bs : List Byte}
    (source : Octets base src len bs s) (positive : 0 < bs.length) (ptr : s.gpr .r4 = src) :
    WP isa (.block [.ldrb .r3 .r4 0, .cmp .r3 (.imm 0)]) s fun t =>
      (t.gpr .r3 = (bs.getD 0 0).setWidth 32 ∧ t.z = decide (bs.getD 0 0 = 0) ∧ t.mem = s.mem) ∧ Rest [.r3] s t := by
  have read : InRegions (s.rd ++ s.wr) (State.addr src) 1 := by
    obtain ⟨r, hr, contains⟩ := source.readable
    exact ⟨r, hr, contains.byte (by simp only [BitVec.sub_self, BitVec.toNat_zero]; exact positive)⟩
  have value : s.mem (State.addr src) = bs.getD 0 0 := by
    have byte := source.byte 0 positive
    change s.mem (State.addr src + 0#64) = bs[0] at byte
    rw [BitVec.add_zero] at byte
    simpa only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem positive, Option.getD_some] using byte
  refine withRest_all [.r3] ?_ (by rfl) (by rfl)
  refine wp_ldrb (a := State.addr src) (by decide) (by rw [ptr, BitVec.add_zero]) read fun u loaded => ?_
  ffrun [loaded.gpr, value, loaded.mem]
  exact byteZero32 _

theorem scanCount_ok (s : State) {n : Nat} (positive : 0 < n) (fits : n < 2 ^ 32)
    (count : s.gpr .r6 = BitVec.ofNat 32 n) :
    WP isa (.block [.cmp .r6 (.imm 1)]) s fun t => (t.z = decide (n = 1) ∧ t.mem = s.mem) ∧ Rest [] s t := by
  refine withRest_all [] ?_ (by rfl) (by rfl)
  ffrun [count]
  exact countOne32 positive fits

theorem scanStop_ok (s : State) : WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.stop s fun t =>
    (t.z = true ∧ t.mem = s.mem) ∧ Rest [.r11] s t := by
  refine withRest_all [.r11] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.stop VG.Impl.Ffdh.Arm.PublicScan.stop
  ffrun []

theorem scanAdvance_ok (s : State) {n : Nat} (positive : 0 < n)
    (count : s.gpr .r6 = BitVec.ofNat 32 n) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.advance s fun t =>
      (t.gpr .r4 = s.gpr .r4 + 1 ∧ t.gpr .r6 = BitVec.ofNat 32 (n - 1) ∧ t.z = false ∧ t.mem = s.mem) ∧
      Rest [.r4, .r6, .r11] s t := by
  refine withRest_all [.r4, .r6, .r11] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.advance VG.Impl.Ffdh.Arm.PublicScan.advance
  ffrun [count]
  exact Offset.ofNat_sub_ofNat (by omega : 1 ≤ n)

end VG.Proof.Ffdh.Arm
