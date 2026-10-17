module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Sm4.X86_64.Layers
meta import VerifiedGarbage.Impl.Sm4.X86_64.Layers

/-!
# SM4 on X86_64: the layers every function shares, as literals

The transposes and four rounds in each direction (`materialize_value`),
evaluated once here: the literals of the functions (`Lit.lean`) and the
checks of the transposes (`Linear.lean`) read them.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

materialize_value Impl.Sm4.X86_64.toBs
materialize_value Impl.Sm4.X86_64.fromBs
materialize_value encRounds := Impl.Sm4.X86_64.rounds4 .enc
materialize_value keyRounds := Impl.Sm4.X86_64.rounds4 .key

end VG.Proof.Sm4.X86_64
