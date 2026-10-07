import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead

namespace VG.Proof.Weierstrass.AArch64.Forward.Arithmetic
noncomputable def cases : Cases
  | .doubleRR => ArithmeticRR.caseProof
  | .mixedHead => ArithmeticMixedHead.caseProof
  | .mixedTail => ArithmeticMixedTail.caseProof
  | .jacHead => ArithmeticJacHead.caseProof
  | .jacTail => ArithmeticJacTail.caseProof
  | .tableHead => ArithmeticTableHead.caseProof
  | .tableTail => ArithmeticTableTail.caseProof
  | .cachedHead => ArithmeticCachedHead.caseProof

end VG.Proof.Weierstrass.AArch64.Forward.Arithmetic
