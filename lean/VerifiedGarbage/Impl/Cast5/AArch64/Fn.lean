module

public import VerifiedGarbage.Impl.Cast5.AArch64.FbFinal
public import VerifiedGarbage.Impl.Cast5.AArch64.Modes
public import VerifiedGarbage.Impl.Cast5.AArch64.Tbl
public import VerifiedGarbage.Impl.Cast5.AArch64.TblModes
public import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.TCB.Code

/-!
# Cast5 on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/Cast5/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.Cast5.AArch64.Fn

open VG.AArch64
open VG.Impl.Residue.AArch64

/-- `c`, then what CAST5-OFB leaves in its registers cleared. -/
def ofbCleared (c : Prog isa) : Prog isa :=
  withClears [.x4, .x6, .x7, .x10, .x13, .x14, .x15]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v16, .v17, .v18, .v19] (some .x4) c

def ofbBase : Prog isa :=
  ofbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.ofb)

def ofb : Prog isa := withScrub 112 ofbBase

def ofbFinalBase : Prog isa :=
  ofbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.ofbFinal)

def ofbFinal : Prog isa := withScrub 112 ofbFinalBase

def tblCleared (c : Prog isa) : Prog isa :=
  withClears [.x6, .x8, .x9] [.v0, .v1, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22,
    .v23, .v24, .v25, .v26, .v27] (some .x6) c

def cbcDecryptChained : Prog isa :=
  tblCleared (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x5 28 Impl.Cast5.AArch64.Tbl.cbcDecryptChained)

def cbcEncryptChainedBase : Prog isa :=
  ofbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cbcEncryptChained)

def cbcEncryptChained : Prog isa := withScrubG 112 [6] cbcEncryptChainedBase

def cfbDecrypt : Prog isa :=
  tblCleared (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x5 28 Impl.Cast5.AArch64.Tbl.cfbDecrypt)

def cfbDecryptFinalBase : Prog isa :=
  ofbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cfbDecryptFinal)

def cfbDecryptFinal : Prog isa := withScrubG 112 [6] cfbDecryptFinalBase

def cfbEncryptBase : Prog isa :=
  ofbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cfbEncrypt)

def cfbEncrypt : Prog isa := withScrubG 112 [6] cfbEncryptBase

def cfbEncryptFinalBase : Prog isa :=
  ofbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cfbEncryptFinal)

def cfbEncryptFinal : Prog isa := withScrubG 112 [6] cfbEncryptFinalBase

/-- `c`, then the clears of what both directions leave. -/
def ecbCleared (c : Prog isa) : Prog isa :=
  withClearsHi [.x6, .x9, .x10, .x13, .x15]
    [.v0, .v1, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v27] (some .x6) .x6 [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15] c

def ecbDecrypt : Prog isa := ecbCleared Impl.Cast5.AArch64.Tbl.ecbDecrypt

def ecbEncrypt : Prog isa := ecbCleared Impl.Cast5.AArch64.Tbl.ecbEncrypt

end VG.Impl.Cast5.AArch64.Fn
