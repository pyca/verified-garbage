module

public import VerifiedGarbage.Impl.Poly1305.Arm
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Poly1305.Arm
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# Poly1305 on Arm: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Poly1305.Arm.init
-- The code of each kind of arithmetic: the baseline's, and `umaal`'s.
materialize_code armPoly1305Blocks := Impl.Poly1305.Arm.blocks false
materialize_code armPoly1305BlocksU := Impl.Poly1305.Arm.blocks true
materialize_code armPoly1305Update := Impl.Poly1305.Arm.update false
materialize_code armPoly1305UpdateU := Impl.Poly1305.Arm.update true
materialize_code armPoly1305Finalize := Impl.Poly1305.Arm.finalize false
materialize_code armPoly1305FinalizeU := Impl.Poly1305.Arm.finalize true

end VG
