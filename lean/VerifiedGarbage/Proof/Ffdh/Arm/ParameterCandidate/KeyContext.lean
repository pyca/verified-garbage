module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Bind RSA's native key-array registers to FFDH's existing Montgomery
allocation. Register setup changes neither memory nor argument slots. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

private theorem nativeKeyWords (w : Nat) :
    (BitVec.ofNat 32 w <<< 1) + 2 = BitVec.ofNat 32 (2 * w + 2) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 32 w * BitVec.ofNat 32 2 + BitVec.ofNat 32 2 = _
  rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
  congr 1
  omega

private theorem nativeKeyStride (w : Nat) :
    (BitVec.ofNat 32 (2 * w + 2) + 2) <<< 2 = BitVec.ofNat 32 (8 * (w + 2)) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change (BitVec.ofNat 32 (2 * w + 2) + BitVec.ofNat 32 2) * BitVec.ofNat 32 4 = _
  rw [BitVec.ofNat_add_ofNat, BitVec.ofNat_mul_ofNat]
  congr 1
  omega

theorem keyContext_ok (s : State) (base : BitVec 32) (w : Nat)
    (readBase : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (saved : s.mem.readW (State.addr s.sp) 32 = base)
    (readWidth : InRegions (s.rd ++ s.wr) (State.addr (base + 48#32)) 4)
    (width : s.mem.readW (State.addr (base + 48#32)) 32 = BitVec.ofNat 32 w) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.keyContext) s fun t =>
      (t.gpr .r0 = base ∧ t.gpr .r8 = base + 96#32 ∧
        t.gpr .r9 = BitVec.ofNat 32 (2 * w + 2) ∧ t.gpr .r7 = BitVec.ofNat 32 (8 * (w + 2)) ∧
        t.mem = s.mem) ∧ Rest [.r0, .r7, .r8, .r9] s t := by
  refine withRest_all [.r0, .r7, .r8, .r9] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.keyContext VG.Impl.Rsa.Arm.Keys.stride
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, readBase, saved, readWidth, width,
    nativeKeyWords w, nativeKeyStride w, show (96 : BitVec 32) = 96#32 from rfl]

end VG.Proof.Ffdh.Arm.ParameterCandidate
