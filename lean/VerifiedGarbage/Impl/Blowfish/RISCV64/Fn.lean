module

public import VerifiedGarbage.Impl.Blowfish.RISCV64
public import VerifiedGarbage.Impl.Blowfish.RISCV64.FbFinal
public import VerifiedGarbage.Impl.Blowfish.RISCV64.Modes
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-! # Blowfish on RISC-V: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.RISCV64.scrubAll rb W`: the `W`
bytes of stack its frames use zeroed), and the caller-saved registers
cleared but the `rb` bits of the result, so that it returns without secret
residue. -/

@[expose] public section

namespace VG.Impl.Blowfish.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll)

/-- `Spec.Blowfish.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  scrubAll 0 4176 Impl.Blowfish.RISCV64.expandKey

/-- `Spec.Blowfish.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  scrubAll 0 4256 Impl.Blowfish.RISCV64.encrypt

/-- `Spec.Blowfish.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  scrubAll 0 4256 Impl.Blowfish.RISCV64.decrypt

/-- `Spec.Blowfish.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  scrubAll 0 4240 Impl.Blowfish.RISCV64.cbcEncryptChained

/-- `Spec.Blowfish.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  scrubAll 0 4336 Impl.Blowfish.RISCV64.cbcDecryptChained

/-- `Spec.Blowfish.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  scrubAll 0 4240 Impl.Blowfish.RISCV64.cfbEncrypt

/-- `Spec.Blowfish.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  scrubAll 0 4336 Impl.Blowfish.RISCV64.cfbDecrypt

/-- `Spec.Blowfish.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrubAll 0 4240 Impl.Blowfish.RISCV64.cfbEncryptFinal

/-- `Spec.Blowfish.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrubAll 0 4240 Impl.Blowfish.RISCV64.cfbDecryptFinal

/-- `Spec.Blowfish.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  scrubAll 0 4240 Impl.Blowfish.RISCV64.ofb

/-- `Spec.Blowfish.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  scrubAll 0 4240 Impl.Blowfish.RISCV64.ofbFinal

end VG.Impl.Blowfish.RISCV64.Fn
