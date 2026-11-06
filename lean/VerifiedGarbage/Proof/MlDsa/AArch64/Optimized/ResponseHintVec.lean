module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintWord
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

theorem word_or (a b : BitVec 128) (e : Nat) :
    vword (a ||| b) e=vword a e ||| vword b e := by
  simp only [vword,BitVec.extractLsb'_or]

theorem word_not (a : BitVec 128) {e : Nat} (he : e<4) :
    vword (~~~a) e = ~~~vword a e := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [vword,BitVec.getLsbD_extractLsb',BitVec.getLsbD_not]
  simp (disch := omega) only [decide_eq_true,Bool.true_and]

end VG.Proof.MlDsa.AArch64.Optimized.Response
