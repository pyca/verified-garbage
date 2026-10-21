module

public import VerifiedGarbage.Impl.Bignum.X86.PublicPower
public import VerifiedGarbage.Proof.Mont.X86.PowerTiming
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext

import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Mont.X86.ExponentTimingBlocks

/-! # Constant-time arithmetic in the compact public RSA workspace -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Proof.Mont.X86.Dynamic

def setupHint : VG.Taint.Hint VG.X86.Taint.T :=
  .seq (workspaceTaint false) (.block [])
    (.seq (workspaceTaint false) (oneHint false) powerHint)

theorem setup_check (n : Nat) :
    VG.Taint.check taint (workspaceTaint false) (setup n) setupHint = some counterEndTaint :=
  exponent_check_seq taint (setupInverse_taint false (slot n 0) inverseOffset) (by rfl)
    (exponent_check_seq taint (one_check false n (slot n 4)) (by rfl)
      (powerTwo_check (modulus n) (slot n 2) (slot n 5) (128 * n)))

end VG.Proof.Bignum.X86.PublicContext
