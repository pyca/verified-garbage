module

public import VerifiedGarbage.Impl.Scrub.RISCV64
public import VerifiedGarbage.Impl.Sm4.RISCV64.CtrFinal
public import VerifiedGarbage.Impl.Sm4.RISCV64.Ecb
public import VerifiedGarbage.Impl.Sm4.RISCV64.ExpandKey
public import VerifiedGarbage.Impl.Sm4.RISCV64.FbFinal
public import VerifiedGarbage.Impl.Sm4.RISCV64.Modes
public import VerifiedGarbage.Impl.StackScratch.RISCV64

/-! # SM4 on RISC-V: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.RISCV64.scrubAll rb W`: the `W`
bytes of stack its frames use zeroed; or `Impl.Scrub.RISCV64.scrubSel rb
fs`: of the stack its frames use, only the runs of doublewords `fs` that the
residue analysis (`RISCV64.rtaint`) finds may differ between two runs
zeroed), and the caller-saved registers cleared but the `rb` bits of the
result, so that it returns without secret residue. -/

@[expose] public section

namespace VG.Impl.Sm4.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll scrubSel)

/-- `Spec.Sm4.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  scrubSel 0 []
    (Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a2 396 Impl.Sm4.RISCV64.expandKey)

/-- `Spec.Sm4.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  scrubSel 0 []
    (Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a3 396 (Impl.Sm4.RISCV64.ecb .encrypt))

/-- `Spec.Sm4.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  scrubSel 0 []
    (Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a3 396 (Impl.Sm4.RISCV64.ecb .decrypt))

/-- `Spec.Sm4.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  scrubAll 0 3248 Impl.Sm4.RISCV64.cbcEncryptChained

/-- `Spec.Sm4.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  scrubAll 0 3248 Impl.Sm4.RISCV64.cbcDecryptChained

/-- `Spec.Sm4.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  scrubAll 0 3248 Impl.Sm4.RISCV64.cfbEncrypt

/-- `Spec.Sm4.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  scrubAll 0 3248 Impl.Sm4.RISCV64.cfbDecrypt

/-- `Spec.Sm4.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrubAll 0 3248 Impl.Sm4.RISCV64.cfbEncryptFinal

/-- `Spec.Sm4.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrubAll 0 3248 Impl.Sm4.RISCV64.cfbDecryptFinal

/-- `Spec.Sm4.ctrApi`'s function as emitted. -/
def ctr : Prog isa :=
  scrubAll 0 3248 Impl.Sm4.RISCV64.ctr

/-- `Spec.Sm4.ctrFinalApi`'s function as emitted. -/
def ctrFinal : Prog isa :=
  scrubAll 0 3328 (Impl.StackScratch.RISCV64.withStackScratchWiped 80 .a4 10 Impl.Sm4.RISCV64.ctrFinal)

/-- `Spec.Sm4.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  scrubAll 0 3248 Impl.Sm4.RISCV64.ofb

/-- `Spec.Sm4.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  scrubAll 0 3248 Impl.Sm4.RISCV64.ofbFinal

end VG.Impl.Sm4.RISCV64.Fn
