module

public import VerifiedGarbage.Impl.Idea.AArch64
public import VerifiedGarbage.Impl.Idea.AArch64.FbFinal
public import VerifiedGarbage.Impl.Idea.AArch64.Modes
public import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Idea on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/Idea/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.Idea.AArch64.Fn

open VG.AArch64
open VG.Impl.Scrub.AArch64

def cbcDecryptChained : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x8, .x9, .x10, .x11, .x12] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cbcDecryptChained)

def cbcEncryptChained : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cbcEncryptChained)

def cfbDecrypt : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbDecrypt)

def cfbDecryptFinal : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x9, .x10, .x11, .x12, .x13, .x14] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbDecryptFinal)

def cfbEncrypt : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbEncrypt)

def cfbEncryptFinal : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x9, .x10, .x11, .x12, .x13, .x14] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbEncryptFinal)

def ofb : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.ofb)

def ofbFinal : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x9, .x10, .x11, .x12, .x13, .x14] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.ofbFinal)

/-- `ecb`, then what it leaves cleared. -/
def ecb : Prog isa :=
  withClears [.x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14]
    [] none Impl.Idea.AArch64.ecb

/-- `expandKey`, then what it leaves cleared. -/
def expandKey : Prog isa :=
  withClears [.x9, .x11]
    [] none Impl.Idea.AArch64.expandKey

/-- `invertKey`, then what it leaves cleared. -/
def invertKey : Prog isa :=
  withClears [.x3, .x4, .x5, .x6, .x9, .x11, .x12]
    [] none Impl.Idea.AArch64.invertKey

end VG.Impl.Idea.AArch64.Fn
