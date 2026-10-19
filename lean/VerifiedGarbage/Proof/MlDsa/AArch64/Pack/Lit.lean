module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Encode
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Encode
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-!
# ML-DSA on AArch64: the encodings as literals

The code of the packing functions, built by functions of the width, as
literals (`materialize_code`, `Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG

materialize_code Impl.MlDsa.AArch64.Pack.simpleBitPack
materialize_code Impl.MlDsa.AArch64.Pack.bitPack
materialize_code Impl.MlDsa.AArch64.Pack.bitUnpack
materialize_code Impl.MlDsa.AArch64.Pack.unpackT1

end VG
