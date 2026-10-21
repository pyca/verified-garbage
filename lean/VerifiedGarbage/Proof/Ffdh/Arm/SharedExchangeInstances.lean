module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangePrograms
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeVerified

/-! The backend's caller transformation preserves shared Montgomery calls. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm

def calledCode (b : MontBackend) : Prog isa := b.caller.code (code b)

theorem called_verified (b : MontBackend) :
    Verified target (calledCode b) (Spec.Ffdh.exchangeContract abi 176) :=
  b.caller.verified (verified b)

theorem called_stack (b : MontBackend) : FrameStack.armStack (calledCode b) ≤ 176 :=
  Nat.le_trans (b.caller.stack_le _) (stack_ok b)

end VG.Proof.Ffdh.Arm.SharedExchange
