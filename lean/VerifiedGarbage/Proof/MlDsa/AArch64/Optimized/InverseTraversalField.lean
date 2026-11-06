module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Arithmetic

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttSpec
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith


namespace InverseTraversal

theorem ofInt_negZetaNat (k : Nat) : ofInt (negZetaNat k : Int) = -zetas k := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [VG.Proof.MlDsa.KeyGen.ofInt_val]
  rw [Int.emod_eq_of_lt (by omega) (by have := negZetaNat_lt k; change _<8380417 at this; omega)]
  exact congrArg (fun n : Nat => (n : Int)) (negZetaNat_eq k)

end InverseTraversal

end VG.Proof.MlDsa.AArch64.Optimized
