module

public import VerifiedGarbage.Proof.X25519.Limbs -- shake: keep (re-exported below for the PPC64LE proofs' `open`s)

/-!
# X25519 on PPC64LE: numbers of 32-bit limbs

`Proof/X25519/Limbs.lean`, which the RISC-V implementation shares, under this
target's namespace, which the proofs built on it open.
-/

public section

namespace VG.Proof.X25519.PPC64LE

export VG.Proof.X25519 (carry_le chain chain_lt chain_succ chain_val foldC foldC_le fourP fourP_ge fourP_le frA frR frS frY freeze_facts mask31 mask31_facts out out_lt pow32_succ rowAcc rowAcc_lt rowC rowC_le row_val sel subC subC_facts sum_lt tailL tail_facts val32 val32_add val32_add_head val32_append val32_cmul val32_congr val32_div val32_foldC val32_fourP val32_head val32_lt val32_mono val32_succ val32_zero_fn)

end VG.Proof.X25519.PPC64LE
