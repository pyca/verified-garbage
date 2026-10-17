module

public import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.X86.Modes
meta import VerifiedGarbage.Impl.TripleDes.X86.Modes
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.X86.Taint
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# Triple DES-CBC on x86 (32-bit): the code as literals

The code of CBC encryption and decryption as literals (`materialize_code`),
which the checks of the whole functions (`taint_decide`, `lit_decide`) read
rather than build the code again.
-/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.X86.cbcEncryptChained
materialize_code Impl.TripleDes.X86.cbcDecryptChained

end VG
