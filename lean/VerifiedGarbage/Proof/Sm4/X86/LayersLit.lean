module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Sm4.X86.Layers
meta import VerifiedGarbage.Impl.Sm4.X86.Layers

/-!
# SM4 on X86: the layers every function shares, as literals

The transposes and four rounds in each direction (`materialize_value`),
evaluated once here: the literals of the functions (`Lit.lean`) and the
checks of the transposes (`Linear.lean`) read them.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

materialize_value Impl.Sm4.X86.toBs
materialize_value Impl.Sm4.X86.fromBs
materialize_value encRounds := Impl.Sm4.X86.rounds4 .enc
materialize_value keyRounds := Impl.Sm4.X86.rounds4 .key

end VG.Proof.Sm4.X86
