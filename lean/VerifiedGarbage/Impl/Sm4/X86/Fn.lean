module

public import VerifiedGarbage.Impl.Sm4.X86.ExpandKey
public import VerifiedGarbage.Impl.Sm4.X86.Ecb
public import VerifiedGarbage.Impl.Sm4.X86.Modes
public import VerifiedGarbage.Impl.Sm4.X86.Fb
public import VerifiedGarbage.Impl.Sm4.X86.FbFinal
public import VerifiedGarbage.Impl.Sm4.X86.Ctr
public import VerifiedGarbage.Impl.Sm4.X86.CtrFinal
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-! # SM4 on x86 (32-bit): the functions as emitted

Each function runs with its working space in a frame on the stack, wiped
before it returns (`withStackScratchWiped`), and is followed by its cleanup.
Key expansion calls nothing in its frame, so its cleanup clears the
registers a callee may change alone (`Impl.Scrub.X86.scrub 0`). The others'
(`Impl.Scrub.X86.scrubSel 0 W ws`, `Impl/Scrub/X86/Sel.lean`) also zero, of
the `W` bytes of stack below `esp` that their contract reserves, the
doublewords `ws` that the residue analysis finds they may leave different in
two runs (the header of their frame, and the frames of the calls of
`vg_sm4_prepare_keys`, `vg_sm4_crypt_prepared` and, for `vg_sm4_ctr_final`,
`vg_sm4_ctr_core` below it), and the registers a callee may change cleared,
so that it returns without secret residue. None returns a
result. -/

@[expose] public section

namespace VG.Impl.Sm4.X86.Fn

open VG.X86

/-- The doublewords of the stack below `esp` that the residue analysis finds
each function may leave different in two runs: of the 1512 bytes ECB
reserves, … -/
def ecbWords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- … of the 1516 bytes the CBC, CFB128, OFB and CTR functions reserve, … -/
def modeWords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- … and of the 1592 bytes of `vg_sm4_ctr_final` calling the baseline's
`vg_sm4_ctr_core`, whose call leaves its frames too. -/
def ctrFinalWords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389]

/-- `Spec.Sm4.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  Impl.Scrub.X86.scrub 0 (Impl.StackScratch.X86.withStackScratchWiped 1448 2 358 Impl.Sm4.X86.expandKey)

/-- `Spec.Sm4.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1512 ecbWords
    (Impl.StackScratch.X86.withStackScratchWiped 1492 3 368 (Impl.Sm4.X86.ecb .encrypt))

/-- `Spec.Sm4.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1512 ecbWords
    (Impl.StackScratch.X86.withStackScratchWiped 1492 3 368 (Impl.Sm4.X86.ecb .decrypt))

/-- `Spec.Sm4.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1516 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cbcEncryptChained)

/-- `Spec.Sm4.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1516 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cbcDecryptChained)

/-- `Spec.Sm4.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1516 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbEncrypt)

/-- `Spec.Sm4.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1516 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbDecrypt)

/-- `Spec.Sm4.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1516 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbEncryptFinal)

/-- `Spec.Sm4.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1516 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbDecryptFinal)

/-- `Spec.Sm4.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1516 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ofb)

/-- `Spec.Sm4.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1516 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ofbFinal)

/-- `Spec.Sm4.ctrApi`'s function as emitted. -/
def ctr : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1516 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ctr)

/-- `Spec.Sm4.ctrFinalApi`'s function as emitted, calling the implementation
`core` of `vg_sm4_ctr`'s code as `name`, and zeroing the doublewords `ws`
that the residue analysis finds it may leave different with it. -/
def ctrFinal (name : String) (core : Prog isa) (ws : List Nat) : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1592 ws
    (Impl.StackScratch.X86.withStackScratchWiped 56 4 8 (Impl.Sm4.X86.ctrFinal name core))

end VG.Impl.Sm4.X86.Fn
