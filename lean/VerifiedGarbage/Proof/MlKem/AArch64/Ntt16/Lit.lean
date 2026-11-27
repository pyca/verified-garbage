module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Forward
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Inverse
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Forward
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Inverse
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.TCB.AArch64.Isa

/-! # The NTTs' code and tables, as literals -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Impl.MlKem.AArch64.Ntt16

/-- The rows of a table, as lists of eight halfwords. -/
def chunks (h : List Nat) : List (List Nat) :=
  (List.range (h.length / 8)).map fun i => (h.drop (8 * i)).take 8

end VG.Proof.MlKem.AArch64.Ntt16

materialize_value VG.Impl.MlKem.AArch64.Ntt16.Forward.words
materialize_value VG.Impl.MlKem.AArch64.Ntt16.Inverse.words

namespace VG.Proof.MlKem.AArch64.Ntt16
open VG VG.AArch64 VG.Impl.MlKem.AArch64.Ntt16

materialize_value Forward.body
materialize_value Inverse.body
materialize_code Forward.code
materialize_code Inverse.code
materialize_value fwdRows := chunks Forward.rows
materialize_value invRows := chunks Inverse.rows

end VG.Proof.MlKem.AArch64.Ntt16
