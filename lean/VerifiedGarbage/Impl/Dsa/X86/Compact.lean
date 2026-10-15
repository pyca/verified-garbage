module

public import VerifiedGarbage.Impl.Dsa.X86.DigestPad

/-! # One arithmetic body per key size

Public digest-prefix dispatch copies into a 32-byte zero-prefixed buffer.
Both arithmetic bodies then consume that fixed-width value. The padding
buffer occupies unused caller scratch space beyond the arithmetic region.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Compact
open VG VG.X86

def sized (signing : Bool) (pLen qLen : Nat) : Prog isa :=
  .seq (Shape.check pLen qLen)
    (.ite .e (Entry.failure signing)
      (.seq (DigestPad.dispatch 32)
        (if signing then SignVerify.signBody pLen qLen 32 else SignVerify.verifyBody pLen qLen 32)))

def widthDispatch (signing : Bool) : List (Nat × Nat) → Prog isa
  | [] => Entry.failure signing
  | (pLen, qLen) :: rest => .seq (Entry.widthMatch pLen qLen)
      (.ite .e (sized signing pLen qLen) (widthDispatch signing rest))

def operation (signing : Bool) : Prog isa := Core.sequence [
  .block (if signing then Entry.signEntry else Entry.verifyEntry),
  widthDispatch signing [(128, 20), (256, 28), (256, 32), (384, 32)],
  .block Entry.restore]

end VG.Impl.Dsa.X86.Compact
