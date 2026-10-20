module

public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! The public space needed by a call of shared Montgomery arithmetic. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

structure CallStack (base : BitVec 32) (len : Nat) (s : State) : Prop where
  fit : 48 ≤ s.sp.toNat
  separate : (FrameStack.belowA s.sp 48).Disjoint ⟨State.addr base, 8 * len⟩

theorem CallStack.of_rest {base : BitVec 32} {len : Nat} {s t : State} {rs : List Reg}
    (h : CallStack base len s) (rest : Rest rs s t) : CallStack base len t := by
  exact ⟨by rw [rest.sp]; exact h.fit, by rw [rest.sp]; exact h.separate⟩

end VG.Proof.Bignum.Arm
