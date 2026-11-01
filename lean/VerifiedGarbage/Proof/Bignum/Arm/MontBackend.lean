module

public import VerifiedGarbage.Proof.Bignum.Arm.MontCallEntry
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.CallerTransform
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! # A callable runtime-width Montgomery arithmetic backend -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm
open VG.Proof.Rsa.Mont (numAt Operand Keeps)

structure MontBackend where
  mul : Prog isa
  verified : Verified target mul (Proof.Rsa.Mont.mulContract abi 40)
  correct : ∀ (s : State) {base : BitVec 32} {len w o a b : Nat},
    CallInput base len w o a b s → Operand o → Operand a → Operand b →
    WP isa mul s fun t => abiPreserved s t ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem
  rawCT : ∀ {base : BitVec 32} {len w o a b : Nat},
    Operand o → Operand a → Operand b →
    RelCT isa (fun s t => CallInput base len w o a b s ∧
      CallInput base len w o a b t ∧ s.sp = t.sp) mul (fun _ _ => True)
  stackOk : FrameStack.armStack mul ≤ 40
  caller : CallerTransform := CallerTransform.identity
  suffix : String
  features : List String

def MontBackend.name (b : MontBackend) : String := "vg_rsa_mont_mul" ++ b.suffix

end VG.Proof.Bignum.Arm
