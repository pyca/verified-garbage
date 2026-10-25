module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeContext
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Load the common RSA byte-copy routine's native arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem shapeCopyHead_ok (s : State) {dst src : BitVec 32} {bs : List Byte} {bits : Nat}
    (h : ShapeContext dst src bs bits s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeCopyHead) s fun t =>
      (t.gpr .r0 = dst ∧ t.gpr .r1 = src ∧ t.gpr .lr = BitVec.ofNat 32 bs.length ∧ t.mem = s.mem) ∧
        Rest [.r0, .r1, .lr] s t := by
  refine withRest_all [.r0, .r1, .lr] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.shapeCopyHead
  ffrun [h.frame.read (d := 4) (by decide), h.frame.read (d := 12) (by decide),
    h.frame.read (d := 16) (by decide), h.frame.saved 4 (by decide),
    h.frame.saved 12 (by decide), h.frame.saved 16 (by decide), shapeValues]

end VG.Proof.Ffdh.Arm.ParameterCandidate
