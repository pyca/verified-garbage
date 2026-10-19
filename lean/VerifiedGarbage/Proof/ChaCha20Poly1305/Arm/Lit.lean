module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.Arm
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.Arm
public import VerifiedGarbage.Proof.ChaCha20.Arm.Lit
meta import VerifiedGarbage.Proof.ChaCha20.Arm.Lit
public import VerifiedGarbage.Proof.Poly1305.Arm.Lit
meta import VerifiedGarbage.Proof.Poly1305.Arm.Lit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

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
