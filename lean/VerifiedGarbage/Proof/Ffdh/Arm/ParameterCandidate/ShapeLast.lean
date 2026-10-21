module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Make the copied candidate odd by setting its final octet's low bit. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem byteOrOne (b : Byte) : ((b.setWidth 32 ||| (1 : BitVec 32)).setWidth 8) = b ||| 1 := by
  rw [BitVec.setWidth_or]
  simp

theorem shapeLast_ok (s : State) (n : Nat)
    (slotRead : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12)) 4)
    (slot : s.mem.readW (State.addr (s.sp + 12)) 32 = BitVec.ofNat 32 n)
    (read : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r4 + BitVec.ofNat 32 n - 1)) 1)
    (write : InRegions s.wr (State.addr (s.gpr .r4 + BitVec.ofNat 32 n - 1)) 1) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeLast) s fun t =>
      (t.gpr .r4 = s.gpr .r4 + BitVec.ofNat 32 n - 1 ∧
        t.mem = s.mem.writeW (State.addr (s.gpr .r4 + BitVec.ofNat 32 n - 1))
          (s.mem (State.addr (s.gpr .r4 + BitVec.ofNat 32 n - 1)) ||| 1)) ∧
        Rest [.r3, .r4, .r5] s t := by
  refine withRest [.r3, .r4, .r5] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeLast : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.shapeLast
  ffrun [show (12#32) = (12 : BitVec 32) from rfl, BitVec.add_zero,
    slotRead, slot, read, write, byteOrOne]

end VG.Proof.Ffdh.Arm.ParameterCandidate
