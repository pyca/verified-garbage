module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Word

/-!
# Ed25519 on PPC64LE: the layout of the working space

Below the field elements (slots at bytes 64–767, `Field.lean`), a
decoding's sign and the scalar's expanded bits at 32–47; the saved
nonvolatile registers and `lr` above `ACC`'s own area, at 1024; and the
tables of points from 1632. Pointers and counters are never stored: they
stay in nonvolatile registers, which the functions called never write, so
that the taint analysis knows they are public (memory is always secret to
it):

* `r14`: a byte pointer (tables, encodings); `r15`: the doublings'
  counter; `r16`: a table index, or the scalar's byte; `r17`: a result (1 or
  0), or a sign; `r18`: decoding's results ANDed, or the output's pointer;
* `r19`: the scalar's pointer; `r26`: the batch counter; `r27`: the
  output's pointer, or decoding's encoding pointer; `r28`: decoding's
  table entry; `r29`–`r31`: verification's `pk`, signature and challenge.

The functions that call the SHA-512 functions keep their own in `r20`–`r25`,
which neither those nor these functions write.
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE

/-- A decoding's sign bit. -/
def SIGN : Nat := 24
/-- The 16 bits of the current batch, one per byte. -/
def BITSB : Nat := 32
/-- The freeze's result and temporary. -/
def FR : Nat := ACC
def FY : Nat := ACC + 32
/-- Where the scalar code's running remainder and candidate are. -/
def SR : Nat := 160
def SD : Nat := 192
/-- Where the functions save `r14`–`r19` and `r26`–`r31` (`SAVE`) and `lr` (`LRS`). -/
def SAVE : Nat := 1024
def LRS : Nat := 1120

end VG.Impl.Ed25519.PPC64LE
