module

public import VerifiedGarbage.Impl.Camellia.X86.ExpandKey
public import VerifiedGarbage.Impl.Camellia.X86.Ecb
public import VerifiedGarbage.Impl.Camellia.X86.Modes
public import VerifiedGarbage.Impl.Camellia.X86.FbFinal
public import VerifiedGarbage.Impl.Camellia.X86.Ctr
public import VerifiedGarbage.Impl.Camellia.X86.CtrFinal
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-! # Camellia on x86 (32-bit): the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`, or
`Impl.Scrub.X86.scrub rb` for code without a frame or calls, or whose frame
it wipes itself with nothing called in it: key expansion): the `W` bytes
of stack below `esp` that its contract reserves zeroed, and the registers
a callee may change cleared but the `rb` bits of the result, so that it
returns without secret residue. -/

@[expose] public section

namespace VG.Impl.Camellia.X86.Fn

open VG.X86

/-- `Spec.Camellia.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  Impl.Scrub.X86.scrub 0 (Impl.StackScratch.X86.withStackScratchWiped 2708 3 672 Impl.Camellia.X86.expandKey)

/-- `Spec.Camellia.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2728 (Impl.StackScratch.X86.withStackScratchWiped 2712 4 672 (Impl.Camellia.X86.ecb .encrypt))

/-- `Spec.Camellia.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2728 (Impl.StackScratch.X86.withStackScratchWiped 2712 4 672 (Impl.Camellia.X86.ecb .decrypt))

/-- `Spec.Camellia.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2772 (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cbcEncryptChained)

/-- `Spec.Camellia.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2772 (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cbcDecryptChained)

/-- `Spec.Camellia.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2772 (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbEncrypt)

/-- `Spec.Camellia.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2772 (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbDecrypt)

/-- `Spec.Camellia.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2772 (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbEncryptFinal)

/-- `Spec.Camellia.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2772 (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbDecryptFinal)

/-- `Spec.Camellia.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2772 (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.ofb)

/-- `Spec.Camellia.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2772 (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.ofbFinal)

/-- `Spec.Camellia.ctrApi`'s function as emitted. -/
def ctr : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2772 (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.ctr)

/-- `Spec.Camellia.ctrFinalApi`'s function as emitted. -/
def ctrFinal : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2856 (Impl.StackScratch.X86.withStackScratchWiped 60 5 8 Impl.Camellia.X86.ctrFinal)

end VG.Impl.Camellia.X86.Fn
