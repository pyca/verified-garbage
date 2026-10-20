module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Reject unsuitable generator-2 candidates from their last octet before
calling RSA's shared reducer modulo three. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm

private theorem lowByte (b : Byte) : b.setWidth 32 &&& 7 = BitVec.ofNat 32 (b.toNat % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega : b.toNat < 2 ^ 32),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b.toNat % 8 < 2 ^ 32)]
  change b.toNat &&& (2 ^ 3 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem residueLow_ok (s : State) (dst : BitVec 32) (n : Nat)
    (readOut : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 4)) 4)
    (readWidth : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12)) 4)
    (out : s.mem.readW (State.addr (s.sp + 4)) 32 = dst)
    (width : s.mem.readW (State.addr (s.sp + 12)) 32 = BitVec.ofNat 32 n)
    (read : InRegions (s.rd ++ s.wr) (State.addr (dst + BitVec.ofNat 32 n - 1)) 1) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.residueLow) s fun t =>
      (t.z = decide ((s.mem (State.addr (dst + BitVec.ofNat 32 n - 1))).toNat % 8 = 3) ∧ t.mem = s.mem) ∧
        Rest [.r2, .r4, .r5] s t := by
  have zero (b : Byte) : ((b.setWidth 32 &&& 7) - 3 == 0) = decide (b.toNat % 8 = 3) := by
    rw [lowByte, sub_beq_zero]
    exact ofNat_beq_eq (by omega) (by decide)
  refine withRest [.r2, .r4, .r5] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterCandidate.residueLow : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  change InRegions (s.rd ++ s.wr) (State.addr (s.sp + 4#32)) 4 at readOut
  change InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12#32)) 4 at readWidth
  change s.mem.readW (State.addr (s.sp + 4#32)) 32 = dst at out
  change s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 n at width
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.residueLow
  ffrun [BitVec.add_zero, readOut, readWidth, out, width, read, zero]

end VG.Proof.Ffdh.Arm.ParameterCandidate
