module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.Arm
public import VerifiedGarbage.Proof.ChaCha20.Arm.Lit
public import VerifiedGarbage.Proof.Poly1305.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.Arm
meta import VerifiedGarbage.Proof.ChaCha20.Arm.Lit
meta import VerifiedGarbage.Proof.Poly1305.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

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
