module

public import VerifiedGarbage.Impl.Sm4.AArch64.Layers
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Sm4.AArch64.Layers
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.AArch64.Target

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
