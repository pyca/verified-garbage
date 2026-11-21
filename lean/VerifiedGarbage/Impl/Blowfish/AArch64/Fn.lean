module

public import VerifiedGarbage.Impl.Blowfish.AArch64
public import VerifiedGarbage.Impl.Blowfish.AArch64.FbFinal
public import VerifiedGarbage.Impl.Blowfish.AArch64.Modes
public import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.TCB.Code

/-!
# Blowfish on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/Blowfish/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.Blowfish.AArch64.Fn

open VG.AArch64
open VG.Impl.Scrub.AArch64

def cbcDecryptChained : Prog isa :=
  withClears [.x6, .x8, .x9] [.v0, .v1, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v28, .v29, .v30, .v31] none (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cbcDecryptChained)

/-- `c`, then the registers a mode leaves secret cleared, the scratch register `xs` among them. -/
def modeCleared (xs : Reg) (c : Prog isa) : Prog isa :=
  withClears [.x6, xs] [.v0, .v1, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v28, .v29, .v30, .v31] none c

def cbcEncryptChained : Prog isa :=
  modeCleared .x7 (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cbcEncryptChained)

def cfbDecrypt : Prog isa :=
  modeCleared .x7 (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbDecrypt)

def cfbDecryptFinal : Prog isa :=
  modeCleared .x7 (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbDecryptFinal)

def cfbEncrypt : Prog isa :=
  modeCleared .x7 (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbEncrypt)

def cfbEncryptFinal : Prog isa :=
  modeCleared .x7 (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbEncryptFinal)

def ecbCleared (c : Prog isa) : Prog isa :=
  withClearsHi [.x6, .x10] [.v0, .v1, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v28, .v29, .v30, .v31] none .x6 [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15] c

def ecbDecrypt : Prog isa :=
  ecbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 256 .x3 32 Impl.Blowfish.AArch64.decrypt)

def ecbEncrypt : Prog isa :=
  ecbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 256 .x3 32 Impl.Blowfish.AArch64.encrypt)

def ofb : Prog isa :=
  modeCleared .x7 (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.ofb)

def ofbFinal : Prog isa :=
  modeCleared .x7 (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.ofbFinal)

def expandKey : Prog isa :=
  withClears [.x6, .x8, .x13]
    [.v0, .v1, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v28, .v29, .v30, .v31] none Impl.Blowfish.AArch64.expandKey

end VG.Impl.Blowfish.AArch64.Fn
