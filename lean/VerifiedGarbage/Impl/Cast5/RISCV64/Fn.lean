module

public import VerifiedGarbage.Impl.Cast5.RISCV64
public import VerifiedGarbage.Impl.Cast5.RISCV64.FbFinal
public import VerifiedGarbage.Impl.Cast5.RISCV64.Modes
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-! # CAST5 on RISC-V: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.RISCV64.scrubAll rb W`: the `W`
bytes of stack its frames use zeroed), and the caller-saved registers
cleared but the `rb` bits of the result, so that it returns without secret
residue. -/

@[expose] public section

namespace VG.Impl.Cast5.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll)

/-- `Spec.Cast5.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  scrubAll 0 0 Impl.Cast5.RISCV64.expandKey

/-- `Spec.Cast5.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  scrubAll 0 0 Impl.Cast5.RISCV64.ecbEncrypt

/-- `Spec.Cast5.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  scrubAll 0 0 Impl.Cast5.RISCV64.ecbDecrypt

/-- `Spec.Cast5.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  scrubAll 0 128 Impl.Cast5.RISCV64.cbcEncryptChained

/-- `Spec.Cast5.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  scrubAll 0 128 Impl.Cast5.RISCV64.cbcDecryptChained

/-- `Spec.Cast5.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  scrubAll 0 128 Impl.Cast5.RISCV64.cfbEncrypt

/-- `Spec.Cast5.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  scrubAll 0 128 Impl.Cast5.RISCV64.cfbDecrypt

/-- `Spec.Cast5.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrubAll 0 128 Impl.Cast5.RISCV64.cfbEncryptFinal

/-- `Spec.Cast5.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrubAll 0 128 Impl.Cast5.RISCV64.cfbDecryptFinal

/-- `Spec.Cast5.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  scrubAll 0 128 Impl.Cast5.RISCV64.ofb

/-- `Spec.Cast5.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  scrubAll 0 128 Impl.Cast5.RISCV64.ofbFinal

end VG.Impl.Cast5.RISCV64.Fn
