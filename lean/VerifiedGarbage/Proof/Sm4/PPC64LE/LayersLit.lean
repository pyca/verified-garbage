module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.Layers
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.Layers
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-!
# SM4 on PPC64LE: the layers every function shares, as literals

The transposes and four rounds in each direction (`materialize_value`),
evaluated once here: the literals of the functions (`Lit.lean`) and the
checks of the transposes (`Linear.lean`) read them.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

materialize_value Impl.Sm4.PPC64LE.toBs
materialize_value Impl.Sm4.PPC64LE.fromBs
materialize_value encRounds := Impl.Sm4.PPC64LE.rounds4 .enc
materialize_value keyRounds := Impl.Sm4.PPC64LE.rounds4 .key

end VG.Proof.Sm4.PPC64LE
