module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Locate the compact small-prime table beyond the primality workspace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (arrAt)

private theorem tableStride (n : Nat) (bound : n ≤ 1024) :
    (((BitVec.ofNat 32 n + 7) >>> 3) + 2) <<< 3 = BitVec.ofNat 32 (8 * ((n + 7) / 8 + 2)) := by
  have shift : BitVec.ofNat 32 (n + 7) >>> 3 = BitVec.ofNat 32 ((n + 7) / 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n + 7 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : (n + 7) / 8 < 2 ^ 32)]
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change (((BitVec.ofNat 32 n + BitVec.ofNat 32 7) >>> 3) + BitVec.ofNat 32 2) * BitVec.ofNat 32 8 = _
  rw [BitVec.ofNat_add_ofNat, shift, BitVec.ofNat_add_ofNat, BitVec.ofNat_mul_ofNat]
  congr 1
  omega

private theorem tableAddress (base : BitVec 32) (n : Nat) :
    (34 * BitVec.ofNat 32 (8 * ((n + 7) / 8 + 2)) + base) + 256 =
      base + BitVec.ofNat 32 (arrAt ((n + 7) / 8) 34) := by
  change (BitVec.ofNat 32 34 * BitVec.ofNat 32 (8 * ((n + 7) / 8 + 2)) + base) + BitVec.ofNat 32 256 = _
  rw [BitVec.ofNat_mul_ofNat, BitVec.add_comm _ base, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have equal : 34 * (8 * ((n + 7) / 8 + 2)) + 256 = arrAt ((n + 7) / 8) 34 := by
    simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes]
    omega
  exact congrArg (fun d : Nat => base + BitVec.ofNat 32 d) equal

theorem tablePointer_ok (s : State) (base : BitVec 32) (n : Nat) (bound : n ≤ 1024)
    (readBase : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (readWidth : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12#32)) 4)
    (savedBase : s.mem.readW (State.addr s.sp) 32 = base)
    (savedWidth : s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 n) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tablePointer) s fun t =>
      (t.gpr .r11 = base + BitVec.ofNat 32 (arrAt ((n + 7) / 8) 34) ∧ t.mem = s.mem) ∧
        Rest [.r0, .r7, .r11] s t := by
  refine withRest_all [.r0, .r7, .r11] ?_ (by rfl) (by rfl)
  have enc256 : encodable (256 : BitVec 32) = true := by decide
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.tablePointer
  ffrun [BitVec.add_zero, readBase, readWidth, savedBase, savedWidth, enc256, tableStride n bound, tableAddress base n]

end VG.Proof.Ffdh.Arm.ParameterCandidate
