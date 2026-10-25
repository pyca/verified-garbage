module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeBits
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

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
