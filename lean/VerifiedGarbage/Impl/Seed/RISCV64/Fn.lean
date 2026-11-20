module

public import VerifiedGarbage.Impl.Scrub.RISCV64
public import VerifiedGarbage.Impl.Seed.RISCV64.Ecb
public import VerifiedGarbage.Impl.Seed.RISCV64.ExpandKey
public import VerifiedGarbage.Impl.Seed.RISCV64.FbFinal
public import VerifiedGarbage.Impl.Seed.RISCV64.Modes
public import VerifiedGarbage.Impl.StackScratch.RISCV64

/-! # SEED on RISC-V: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.RISCV64.scrub rb W`: the `W`
bytes of stack its frames use zeroed; or `Impl.Scrub.RISCV64.scrubSel rb
fs`: of the stack its frames use, only the runs of doublewords `fs` that the
residue analysis (`RISCV64.rtaint`) finds may differ between two runs
zeroed), and the caller-saved registers cleared but the `rb` bits of the
result, so that it returns without secret residue. -/

@[expose] public section

namespace VG.Impl.Seed.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub scrubSel)

/-- `Spec.Seed.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  scrubSel 0 [(1040, [(129, 1)])]
    (Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a2 129 Impl.Seed.RISCV64.expandKey)

/-- `Spec.Seed.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  scrubSel 0 [(1040, [(129, 1)])]
    (Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a3 129 (Impl.Seed.RISCV64.ecb .encrypt))

/-- `Spec.Seed.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  scrubSel 0 [(1040, [(129, 1)])]
    (Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a3 129 (Impl.Seed.RISCV64.ecb .decrypt))

/-- `Spec.Seed.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  scrub 0 1120 Impl.Seed.RISCV64.cbcEncryptChained

/-- `Spec.Seed.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  scrub 0 1360 Impl.Seed.RISCV64.cbcDecryptChained

/-- `Spec.Seed.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  scrub 0 1120 Impl.Seed.RISCV64.cfbEncrypt

/-- `Spec.Seed.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  scrub 0 1360 Impl.Seed.RISCV64.cfbDecrypt

/-- `Spec.Seed.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrub 0 1120 Impl.Seed.RISCV64.cfbEncryptFinal

/-- `Spec.Seed.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrub 0 1120 Impl.Seed.RISCV64.cfbDecryptFinal

/-- `Spec.Seed.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  scrub 0 1120 Impl.Seed.RISCV64.ofb

/-- `Spec.Seed.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  scrub 0 1120 Impl.Seed.RISCV64.ofbFinal

end VG.Impl.Seed.RISCV64.Fn
