module

public import VerifiedGarbage.Impl.Camellia.X86.AesNiWide
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-! # Camellia's wide modes by the AES S-box on x86 (32-bit): the functions as emitted

Each function with its working space in a frame on the stack, which it
wipes (`withStackScratchWiped`), then its cleanup
(`Impl.Scrub.X86.scrubSel rb W ws`): of the `W` bytes of stack below `esp`
that its contract reserves, the doublewords `ws` its code may leave
different in two runs zeroed, and the registers a callee may change
cleared, so that it returns without secret residue.

A function's frame is larger than its working space and header need (888
bytes for 884), so that the working space, which `withStackScratchWiped`
puts 28 bytes above the frame's base for five arguments, is at a multiple
of 16 when `esp` is one at the call: the places and the blocks, at
multiples of 16 in it, which every round loads and stores, then cross no
page, or line of the cache (the keys, as `AesNi.prepare` lays them out
from byte 24 on, are 8 modulo 16). `ctrFramed`'s frame is as it was:
`vg_camellia_ctr_final` calls it from a frame of its own. -/

@[expose] public section

namespace VG.Impl.Camellia.X86.AesNiWide

open VG.X86

/-- `vg_camellia_ctr`'s code, with its working space on the stack: called
as an internal function of its own, `vg_camellia_ctr_core_aesni`. -/
def ctrFramed : Prog isa := Impl.StackScratch.X86.withStackScratchWiped 884 5 214 ctr

namespace Fn

/-- The doublewords of the 892 bytes of stack below `esp` that the residue
analysis finds each function may leave different in two runs: the header
of its working space's frame, and the frame's last doubleword, which
nothing writes. -/
def modeWords : List Nat := [1, 2, 3, 4, 5, 6, 7, 222]

/-- And of the 2856 bytes of `vg_camellia_ctr_final` calling `ctrFramed`:
the header of that call's frame, and what the baseline's leaves of its
own. -/
def ctrFinalWords : List Nat :=
  [472, 473, 474, 475, 476, 477, 478, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705]

/-- `Spec.Camellia.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 892 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 888 5 214 Impl.Camellia.X86.AesNiWide.cbcDecryptChained)

/-- `Spec.Camellia.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 892 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 888 5 214 Impl.Camellia.X86.AesNiWide.cfbDecrypt)

/-- `Spec.Camellia.ctrApi`'s function as emitted. -/
def ctr : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 892 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 888 5 214 Impl.Camellia.X86.AesNiWide.ctr)

end Fn

end VG.Impl.Camellia.X86.AesNiWide
