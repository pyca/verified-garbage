module

public import VerifiedGarbage.Impl.Scrub.RISCV64
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Bitsliced
public import VerifiedGarbage.Impl.TripleDes.RISCV64.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.RISCV64.FbFinal
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Modes

/-! # Triple DES on RISC-V: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.RISCV64.scrub rb W`: the `W`
bytes of stack its frames use zeroed), and the caller-saved registers
cleared but the `rb` bits of the result, so that it returns without secret
residue. -/

@[expose] public section

namespace VG.Impl.TripleDes.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub)

/-- `Spec.TripleDes.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  scrub 0 0 Impl.TripleDes.RISCV64.Key.expandKey

/-- `Spec.TripleDes.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  scrub 0 1056 Impl.TripleDes.RISCV64.Bitslice.encrypt

/-- `Spec.TripleDes.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  scrub 0 1056 Impl.TripleDes.RISCV64.Bitslice.decrypt

/-- `Spec.TripleDes.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  scrub 0 944 Impl.TripleDes.RISCV64.cbcEncryptChained

/-- `Spec.TripleDes.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  scrub 0 1120 Impl.TripleDes.RISCV64.cbcDecryptChained

/-- `Spec.TripleDes.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  scrub 0 944 Impl.TripleDes.RISCV64.cfbEncrypt

/-- `Spec.TripleDes.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  scrub 0 1120 Impl.TripleDes.RISCV64.cfbDecrypt

/-- `Spec.TripleDes.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrub 0 944 Impl.TripleDes.RISCV64.cfbEncryptFinal

/-- `Spec.TripleDes.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrub 0 944 Impl.TripleDes.RISCV64.cfbDecryptFinal

/-- `Spec.TripleDes.cfb8EncryptApi`'s function as emitted. -/
def cfb8Encrypt : Prog isa :=
  scrub 0 944 Impl.TripleDes.RISCV64.cfb8Encrypt

/-- `Spec.TripleDes.cfb8DecryptApi`'s function as emitted. -/
def cfb8Decrypt : Prog isa :=
  scrub 0 944 Impl.TripleDes.RISCV64.cfb8Decrypt

/-- `Spec.TripleDes.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  scrub 0 944 Impl.TripleDes.RISCV64.ofb

/-- `Spec.TripleDes.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  scrub 0 944 Impl.TripleDes.RISCV64.ofbFinal

end VG.Impl.TripleDes.RISCV64.Fn
