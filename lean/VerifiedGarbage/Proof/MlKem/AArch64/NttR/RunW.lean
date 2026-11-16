module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sym
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sound
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Lit
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sym
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-KEM on AArch64: the runs of the 16-bit NTTs of a polynomial stored with 16 bits

The terms a transform of a polynomial stored with 16 bits starts from (`fInW`:
coefficient `p` of the input in halfword `p`),
and what its run leaves in the polynomial (`outW`: the reduced coefficients).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64

/-- `n` chunks, chunk `j`'s halfword `e` the term `f j e`. -/
def packY (f : Nat → Nat → T) (n : Nat) : Nat :=
  (List.range n).foldr (fun j acc => Y.ofFn (f j) + 2 ^ yw * acc) 0

/-- The input, coefficient `p` in halfword `p`. -/
def fInW : Nat := packY (fun j e => lvT 0 (8 * j + e)) 32

materialize_value fInW

/-- The polynomial's halfwords are the reduced coefficients of `NTT`. -/
def outW (σ : St) : Bool :=
  (List.range 32).all fun j => (List.range 8).all fun e => Nat.beq ((σ.chunk 0 j).get e) (outT (8 * j + e))

end VG.Proof.MlKem.AArch64.NttR
