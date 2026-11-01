module

public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Impl.Bignum.Arm.MontCallWith
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallArithmetic
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.CallF

/-! The public dispatcher's arithmetic and timing obligations. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

structure CallArithmeticLaw (arithmetic : Prog isa) : Prop where
  correct : ∀ (s : State) {base : BitVec 32} {len w o a b : Nat}
    (_h : CallBodyReady base len w o a b s)
    (_ho : Operand o) (_ha : Operand a) (_hb : Operand b),
    WP isa arithmetic s fun t =>
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t
  ct : ∀ {base : BitVec 32} {len w o a b : Nat},
    Operand o → Operand a → Operand b → arrAt w 3 + 32 ≤ 8 * len →
    RelCT isa (fun s t => CallBodyReady base len w o a b s ∧
      CallBodyReady base len w o a b t ∧ s.sp = t.sp) arithmetic (fun _ _ => True)
  stack : FrameStack.armStack arithmetic = 0

end VG.Proof.Bignum.Arm
