module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.ChaCha20Poly1305.Arm
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.Arm
public import VerifiedGarbage.Proof.ChaCha20.Arm.Lit
meta import VerifiedGarbage.Proof.ChaCha20.Arm.Lit
public import VerifiedGarbage.Proof.Poly1305.Arm.Lit
meta import VerifiedGarbage.Proof.Poly1305.Arm.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# ChaCha20-Poly1305 on Arm: the code as literals
-/

@[expose] public section

namespace VG

-- The parts of the code that the constant-time proofs analyse on their own.
materialize_code Impl.ChaCha20Poly1305.Arm.sealMain
materialize_code Impl.ChaCha20Poly1305.Arm.openMain
materialize_code Impl.ChaCha20Poly1305.Arm.openEnd
materialize_code Impl.ChaCha20Poly1305.Arm.seal
materialize_code Impl.ChaCha20Poly1305.Arm.open

end VG
