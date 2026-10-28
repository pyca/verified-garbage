module

public import VerifiedGarbage.Proof.X25519.PPC64LE.Limbs -- shake: keep (re-exported for the PPC64LE proofs' `open`s)
public import VerifiedGarbage.Proof.X448.Limbs32 -- shake: keep (re-exported below for the PPC64LE proofs' `open`s)

/-!
# X448 on PPC64LE: numbers of 32-bit limbs

`Proof/X448/Limbs32.lean`, which the RISC-V implementation shares, under this
target's namespace, which the proofs built on it open.
-/

public section

namespace VG.Proof.X448.PPC64LE

export VG.Proof.X448.Limbs32 (pow448 pow448_eq P_eq fold448 rowAcc row_val rowAcc_lt foldC foldC_le foldC_facts foldL val32_foldL fold1 fold1C fold1_facts chain_congr fold1_congr tailL tail_facts fourP val32_fourP subC subC_facts carry_le frR freeze_facts val32_single)

end VG.Proof.X448.PPC64LE
