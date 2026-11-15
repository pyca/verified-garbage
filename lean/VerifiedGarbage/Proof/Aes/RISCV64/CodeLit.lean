module

public import VerifiedGarbage.Impl.Aes.RISCV64.Blocks
public import VerifiedGarbage.Impl.Aes.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Aes.RISCV64.Blocks
meta import VerifiedGarbage.Impl.Aes.RISCV64.ExpandKey
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
# AES on RISC-V, as literals

The code of `vg_aes_ctr32`, `vg_aes_ctr32_to`, `vg_aes_{en,de}crypt_blocks` and
`vg_aes_expand_key_scratch`, built by functions, as literals
(`materialize_code`): the checks that evaluate it (`lit_decide`,
`taint_decide`, here and in the modes that call it) read the literal instead
of building the code again. The four blocks' encryption and decryption
(`encrypt4`, `decrypt4`), which the code of every function over AES has, come
first: the other literals are checked against theirs.

Their constant-time analysis is done here once too, as summaries
(`encrypt4Sum`, `decrypt4Sum`), next to the literals it reads: the checks of
the functions that have them use the summaries (`taint_decide_sum`) in place
of the analysis, and of the code, of the four blocks in each.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

materialize_code encrypt4
materialize_code decrypt4
materialize_code ctr32
materialize_code ctr32To
materialize_code encryptBlocks
materialize_code decryptBlocks
materialize_code expandKey

/-! The constant-time analysis of the four blocks' encryption, from the round keys' address
(`a0`) and the scratch buffer's base (`a5`), which keeps what is public of `a2`–`a4` and `ra`,
where its callers keep their pointers and counts: it writes none of them. -/
open VG.RISCV64 in
taint_summary encrypt4Sum : taint (Taint.ofRegs [.a0, .a5]) encrypt4
  keeping (Taint.ofRegs [.a2, .a3, .a4, .ra])

/-! The same of the four blocks' decryption. -/
open VG.RISCV64 in
taint_summary decrypt4Sum : taint (Taint.ofRegs [.a0, .a5]) decrypt4
  keeping (Taint.ofRegs [.a2, .a3, .a4, .ra])

end VG.Impl.Aes.RISCV64
