module

public import VerifiedGarbage.Proof.X25519.Limbs -- shake: keep (opened by the RISC-V proofs)
public import VerifiedGarbage.Proof.X448.Limbs32 -- shake: keep (re-exported below for the RISC-V proofs' `open`s)

/-!
# X448 on RISCV64: numbers of 32-bit limbs

`Proof/X448/Limbs32.lean`, shared with PPC64LE, under this target's namespace,
which the proofs built on it open.
-/

public section

namespace VG.Proof.X448.RISCV64

export VG.Proof.X448.Limbs32 (pow448 pow448_eq P_eq fold448 rowAcc row_val rowAcc_lt foldC foldC_le foldC_facts foldL val32_foldL fold1 fold1C fold1_facts chain_congr fold1_congr tailL tail_facts fourP val32_fourP subC subC_facts carry_le frR freeze_facts val32_single)

end VG.Proof.X448.RISCV64
