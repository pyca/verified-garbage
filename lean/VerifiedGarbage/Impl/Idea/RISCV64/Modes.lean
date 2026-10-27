module

public import VerifiedGarbage.Impl.Modes.RISCV64.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Idea.RISCV64

/-!
# IDEA's modes on RISC-V

`core`: ECB's block code (`cryptBlock`), inlined, as a core for the modes
(`Impl/Modes/RISCV64/Seq.lean`), running IDEA in place on the block in its
buffer under the subkeys at `a0`, read in place a byte at a time: the
encryption subkeys for encryption, the decryption subkeys
(`vg_idea_invert_key`) for CBC decryption. It sets the mask in `t2` and
points `a1` at the buffer (slot 6, the first of the core's), and uses only
temporaries and argument registers besides. 8 slots in all, with the
modes'.

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and
`cfbDecrypt` (schedule = a0, iv = a1, data = a2, n = a3) are the modes over
it.
-/

@[expose] public section

namespace VG.Impl.Idea.RISCV64

open VG.RISCV64
open VG.Impl.Modes.RISCV64 (sb)

/-- The buffer's block. -/
def bufSlot : Nat := 6

/-- IDEA's core for the modes. -/
def core : Modes.RISCV64.Core where
  prepare := .block []
  crypt := .seq (.block setMask) (.seq (.block [.addi .a1 sb (8 * bufSlot)]) (.block cryptBlock))
  total := 8
  buf := bufSlot
  G := 1
  bw := 2

/-- `vg_idea_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := core.seq (Modes.Mode.cbcEncChained 2)

/-- `vg_idea_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := core.seq (Modes.Mode.cbcDecChained 2)

/-- `vg_idea_ofb`. -/
def ofb : Prog isa := core.seq (Modes.Mode.ofb 2)

/-- `vg_idea_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := core.seq (Modes.Mode.cfbEnc 2)

/-- `vg_idea_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := core.seq (Modes.Mode.cfbDec 2)

end VG.Impl.Idea.RISCV64
