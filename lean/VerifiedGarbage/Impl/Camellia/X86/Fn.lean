module

public import VerifiedGarbage.Impl.Camellia.X86.CtrFinal
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-! # Camellia-CTR of a message's last piece on x86 (32-bit): the function as emitted

`ctrFinal` (`CtrFinal.lean`), with `save` in a frame on the stack, which it
wipes, then its cleanup (`Impl.Scrub.X86.scrubSel rb W ws`): of the `W` bytes
of stack below `esp` that its contract reserves, the doublewords `ws` its code
may leave different in two runs zeroed (`Impl/Scrub/X86/Sel.lean`), and the
registers a callee may change cleared, so that it returns without secret
residue. -/

@[expose] public section

namespace VG.Impl.Camellia.X86.Fn

open VG.X86

/-- `Spec.Camellia.ctrFinalApi`'s function as emitted, calling the
implementation `core` of `vg_camellia_ctr`'s code as `name`, and zeroing the
doublewords `ws` that the residue analysis finds it may leave different with
it. -/
def ctrFinal (name : String) (core : Prog isa) (ws : List Nat) : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1660 ws
    (Impl.StackScratch.X86.withStackScratchWiped 60 5 8 (Impl.Camellia.X86.ctrFinal name core))

end VG.Impl.Camellia.X86.Fn
