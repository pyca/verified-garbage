module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Sm4.AArch64.Layers
meta import VerifiedGarbage.Impl.Sm4.AArch64.Layers

/-!
# SM4 on AArch64: the layers every function shares, as literals

The transposes and four rounds in each direction (`materialize_value`),
evaluated once here: the literals of the functions (`Lit.lean`) and the
checks of the transposes (`Linear.lean`) read them.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

materialize_value Impl.Sm4.AArch64.toBs
materialize_value Impl.Sm4.AArch64.fromBs
materialize_value encRounds := Impl.Sm4.AArch64.rounds4 .enc
materialize_value keyRounds := Impl.Sm4.AArch64.rounds4 .key

end VG.Proof.Sm4.AArch64
