module

public import VerifiedGarbage.Impl.Bignum.Arm.WindowExp

/-! # Three-bit exponentiation through shared Montgomery calls

The table and byte controls are the existing RSA window's; each arithmetic
operation is supplied by the caller, so multiplication and squaring each
have one callable implementation rather than being repeated here.
-/

@[expose] public section
namespace VG.Impl.Bignum.Arm.SharedWindow
open VG VG.Arm

def init (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (smallConst 7 1) (.seq (op 6 4 7) (op 5 1 4))

def tableBody (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (op 1 1 5) (.seq (entryCopy 1) (.block entryNext))

def tablePrepare : Prog isa :=
  .seq (.block tableInit)
    (.seq (.seq (entryCopy 6) (.block entryNext))
      (.seq (.seq (entryCopy 5) (.block entryNext))
        (.seq (.block [.mov .r11 (.imm 1)]) (selectArray 1 1 5))))

def tableBuild (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq tablePrepare (.loop (tableBody op) .ne)

def apply (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq scan (.seq (op 6 6 1) (.block windowReset))

def bit (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (op 6 6 6) (.seq (.block windowBitValue) (.ite .eq (apply op) (.block [])))

def round (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (bit op) (.seq (.block expShift) (.block expDecrement))

def bits (op : Nat → Nat → Nat → Prog isa) : Prog isa := .loop (round op) .ne

def bytes (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .loop (.seq expByteHead (.seq (bits op) (.block expByteNext))) .ne

def phase (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (init op) (.seq (tableBuild op) (.seq (.block windowReset) (.seq (bytes op)
    (.seq (apply op) (op 6 6 7)))))

end VG.Impl.Bignum.Arm.SharedWindow
