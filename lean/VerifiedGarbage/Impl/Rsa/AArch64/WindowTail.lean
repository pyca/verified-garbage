module

public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive

/-! Bitwise tail of the five-bit window prototype; no exponent padding. -/

@[expose] public section
namespace VG.Impl.Rsa.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

/-- Append one bit of the final source bytes and test whether five are ready. -/
def prepareBit (i : Nat) : List Instr :=
  [ldh .x3 Crt.sNib, .lsl .x .x3 .x3 1, ldh .x4 Crt.sV, .lsr .x .x4 .x4 (7 - i),
    movi .x5 1, .logic .and .x .x4 .x4 .x5, .logic .orr .x .x3 .x3 .x4, sth .x3 Crt.sNib,
    ldh .x3 Crt.sBit, .addImm .x .x3 .x3 1, sth .x3 Crt.sBit, .subImm .x .x3 .x3 5]

def takeBit (window : Prog isa) (i : Nat) : Prog isa :=
  .seq (.block (prepareBit i)) (.ite (.zero .x .x3) window (.block []))

/-- Consume the first `n` bits of the final byte, in source order. -/
def tailBits (window : Prog isa) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (tailBits window n) (takeBit window n)

/-- Eight calls share one arithmetic window body. -/
def appliedGroup (window : Prog isa) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.seq (.block (groupDigit (5 * n))) window) (appliedGroup window n)

/-- Load five bytes and consume them with the shared arithmetic window. -/
def appliedBatch (window : Prog isa) : Prog isa :=
  .seq (.block loadGroup) (appliedGroup window 8)

/-- Square once and decrement the public number of pending bits. -/
def finishSquare (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (mul Public.aY Public.aY Public.aY)
    (.block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit])

/-- Complete a partial window without appending any zero exponent bits. -/
def finish (mul : Nat → Nat → Nat → Prog isa) (select : Prog isa) : Prog isa :=
  .seq (.block [ldh .x3 Crt.sBit])
    (.ite (.nonzero .x .x3)
      (.seq (.loop (finishSquare mul) (.nonzero .x .x3))
        (.seq select (mul Public.aY Public.aY Crt.aT))) (.block []))

end VG.Impl.Rsa.AArch64.WindowFive
