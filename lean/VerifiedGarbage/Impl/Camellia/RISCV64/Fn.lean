module

public import VerifiedGarbage.Impl.Camellia.RISCV64.ExpandKey
public import VerifiedGarbage.Impl.Camellia.RISCV64.Ecb
public import VerifiedGarbage.Impl.Camellia.RISCV64.Modes
public import VerifiedGarbage.Impl.Camellia.RISCV64.FbFinal
public import VerifiedGarbage.Impl.Camellia.RISCV64.CtrFinal
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-! # Camellia and its modes on RISC-V: the functions as emitted

Each function, then its cleanup: `Impl.Scrub.RISCV64.scrubAll rb W`, which
zeroes the `W` bytes of stack its contract reserves and clears the
caller-saved registers but the `rb` bits of the result, or, for the key
expansion and ECB, whose code wipes its own scratch space,
`Impl.Scrub.RISCV64.scrubSel rb []`, which clears the registers and none of
the stack (the residue analysis, `RISCV64.rtaint`, finds no doubleword of it
that may differ between two runs). So each returns without secret
residue. -/

@[expose] public section

namespace VG.Impl.Camellia.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll scrubSel)
open VG.Impl.StackScratch.RISCV64 (withStackScratchWiped)

/-- `vg_camellia_expand_key`, as emitted. -/
def expandKey : Prog isa :=
  scrubSel 0 [] (withStackScratchWiped 3200 .a3 400 Impl.Camellia.RISCV64.expandKey)

/-- `vg_camellia_ecb_encrypt`, as emitted. -/
def ecbEncrypt : Prog isa :=
  scrubSel 0 [] (withStackScratchWiped 3200 .a4 400 (Impl.Camellia.RISCV64.ecb .encrypt))

/-- `vg_camellia_ecb_decrypt`, as emitted. -/
def ecbDecrypt : Prog isa :=
  scrubSel 0 [] (withStackScratchWiped 3200 .a4 400 (Impl.Camellia.RISCV64.ecb .decrypt))

/-- `vg_camellia_cbc_encrypt_chained`, as emitted. -/
def cbcEncryptChained : Prog isa := scrubAll 0 3264 Impl.Camellia.RISCV64.cbcEncryptChained

/-- `vg_camellia_cbc_decrypt_chained`, as emitted. -/
def cbcDecryptChained : Prog isa := scrubAll 0 3264 Impl.Camellia.RISCV64.cbcDecryptChained

/-- `vg_camellia_cfb128_encrypt`, as emitted. -/
def cfbEncrypt : Prog isa := scrubAll 0 3264 Impl.Camellia.RISCV64.cfbEncrypt

/-- `vg_camellia_cfb128_decrypt`, as emitted. -/
def cfbDecrypt : Prog isa := scrubAll 0 3264 Impl.Camellia.RISCV64.cfbDecrypt

/-- `vg_camellia_cfb128_encrypt_final`, as emitted. -/
def cfbEncryptFinal : Prog isa := scrubAll 0 3264 Impl.Camellia.RISCV64.cfbEncryptFinal

/-- `vg_camellia_cfb128_decrypt_final`, as emitted. -/
def cfbDecryptFinal : Prog isa := scrubAll 0 3264 Impl.Camellia.RISCV64.cfbDecryptFinal

/-- `vg_camellia_ctr`, as emitted. -/
def ctr : Prog isa := scrubAll 0 3264 Impl.Camellia.RISCV64.ctr

/-- `vg_camellia_ctr_final`, as emitted. -/
def ctrFinal : Prog isa :=
  scrubAll 0 3344 (withStackScratchWiped 80 .a5 10 Impl.Camellia.RISCV64.ctrFinal)

/-- `vg_camellia_ofb`, as emitted. -/
def ofb : Prog isa := scrubAll 0 3264 Impl.Camellia.RISCV64.ofb

/-- `vg_camellia_ofb_final`, as emitted. -/
def ofbFinal : Prog isa := scrubAll 0 3264 Impl.Camellia.RISCV64.ofbFinal

end VG.Impl.Camellia.RISCV64.Fn
