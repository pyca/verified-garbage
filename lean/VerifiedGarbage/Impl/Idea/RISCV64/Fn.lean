module

public import VerifiedGarbage.Impl.Idea.RISCV64
public import VerifiedGarbage.Impl.Idea.RISCV64.FbFinal
public import VerifiedGarbage.Impl.Idea.RISCV64.Modes
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-! # IDEA on RISC-V: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.RISCV64.scrub rb W`: the `W`
bytes of stack its frames use zeroed), and the caller-saved registers
cleared but the `rb` bits of the result, so that it returns without secret
residue. -/

@[expose] public section

namespace VG.Impl.Idea.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub)

/-- `Spec.Idea.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  scrub 0 0 Impl.Idea.RISCV64.expandKey

/-- `Spec.Idea.invertKeyApi`'s function as emitted. -/
def invertKey : Prog isa :=
  scrub 0 0 Impl.Idea.RISCV64.invertKey

/-- `Spec.Idea.ecbApi`'s function as emitted. -/
def ecb : Prog isa :=
  scrub 0 0 Impl.Idea.RISCV64.ecb

/-- `Spec.Idea.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  scrub 0 64 Impl.Idea.RISCV64.cbcEncryptChained

/-- `Spec.Idea.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  scrub 0 64 Impl.Idea.RISCV64.cbcDecryptChained

/-- `Spec.Idea.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  scrub 0 64 Impl.Idea.RISCV64.cfbEncrypt

/-- `Spec.Idea.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  scrub 0 64 Impl.Idea.RISCV64.cfbDecrypt

/-- `Spec.Idea.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrub 0 64 Impl.Idea.RISCV64.cfbEncryptFinal

/-- `Spec.Idea.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrub 0 64 Impl.Idea.RISCV64.cfbDecryptFinal

/-- `Spec.Idea.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  scrub 0 64 Impl.Idea.RISCV64.ofb

/-- `Spec.Idea.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  scrub 0 64 Impl.Idea.RISCV64.ofbFinal

end VG.Impl.Idea.RISCV64.Fn
