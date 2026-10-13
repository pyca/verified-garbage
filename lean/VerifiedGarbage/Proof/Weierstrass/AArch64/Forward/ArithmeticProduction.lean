module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Forward.Arithmetic
theorem cases : Cases
  | .doubleRR => ArithmeticRR.caseProof
  | .mixedHead => ArithmeticMixedHead.caseProof
  | .mixedTail => ArithmeticMixedTail.caseProof
  | .jacHead => ArithmeticJacHead.caseProof
  | .jacTail => ArithmeticJacTail.caseProof
  | .tableHead => ArithmeticTableHead.caseProof
  | .tableTail => ArithmeticTableTail.caseProof
  | .cachedHead => ArithmeticCachedHead.caseProof

end VG.Proof.Weierstrass.AArch64.Forward.Arithmetic
