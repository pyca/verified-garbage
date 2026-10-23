module

public import VerifiedGarbage.Impl.Pbkdf2.Stream.PPC64LE

/-!
# PBKDF2-HMAC over any streaming hash function: PPC64LE implementation of the whole derivation

`pbkdf2(password = r3, password_len = r4, salt = r5, salt_len = r6, c = r7,
out = r8, out_len = r9, scratch = r10)` computes PBKDF2-HMAC (RFC 8018 §5.2)
from the verified functions of one hash function (`Fns`): HMAC's `init` for
a key of any length makes the password's inner and outer states; each block
`i` of the output copies the inner state, absorbs the salt and `INT (i)`
into it and computes `U₁` with HMAC's `finalize`; `T` starts as `U₁`,
`iterate` runs the other `c - 1` steps, and as much of `T` as the output
still needs is copied to `out`.

`scratch` starts with our caller's `r20`–`r25` (`Hash.saveAt 0`), then the
working space of the functions we call (`Wc` bytes, from `scratch + 48`),
then the key's two states, a working state, `U`, `T` and `INT (i)`. Our
variables live in `r20`–`r25`, which every function we call preserves
(HMAC's functions and `iterate` save and restore them, so the analysis of
constant time relates the runs around those calls by their contracts rather
than following the registers through them): `r21` = `scratch`, `r20` =
`salt_len`, `r22` = `c`, `r25` = `salt`, `r23` = where the rest of the
output goes and `r24` = how many bytes of it are left. `c` is a 32-bit
argument whose other bits may be anything: only `iterate` reads it, and only
its low 32 bits. `INT (i)` is kept in `scratch`, big-endian, and incremented
in place (`lwbrx`, `stwbrx`). Whether fewer than `D` bytes of output are
left is the sign of their number minus `D`, which is less than `2⁶³`. Every
address and branch depends only on the pointers and the lengths.
-/

@[expose] public section

namespace VG.Impl.Pbkdf2.Whole.PPC64LE

open VG.PPC64LE
open VG.Impl.MdStream.PPC64LE (mov)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Impl.Hmac.Stream.PPC64LE.Hash (cp32)

/-- The functions PBKDF2 calls, for one hash function: its streaming
functions (`H`, with their sizes), the bytes of working space the functions
we call get (`Wc`), and HMAC's `init` for a key of any length (with its
code), HMAC's `finalize` with its working space as an argument and PBKDF2's
`iterate`, with their names. -/
structure Fns where
  H : Hash
  Wc : Nat
  hiN : String
  hiC : Prog isa
  hfN : String
  itN : String

namespace Fns

variable (F : Fns)

/-- The working space of the functions we call, after our caller's registers. -/
def cO : Nat := 48

/-- The key's inner and outer states and the working state. -/
def st0O : Nat := cO + F.Wc
def st1O : Nat := F.st0O + F.H.S
def stWO : Nat := F.st1O + F.H.S

/-- `U`, `T` and `INT (i)`. -/
def uO : Nat := F.stWO + F.H.S
def tO : Nat := F.uO + F.H.D
def intO : Nat := F.tO + F.H.D

/-- The bytes of `scratch` we use. -/
def bytes : Nat := F.intO + 4

/-- A call of HMAC's `init`. -/
def callHi : Prog isa := .call F.hiN F.hiC

/-- A call of HMAC's `finalize`. -/
def callHf : Prog isa := .call F.hfN F.H.finalize

/-- A call of `iterate`. -/
def callIt : Prog isa := .call F.itN (Stream.PPC64LE.iterate F.H)

/-- Our caller's registers into `scratch`, which `r21` then holds; the
arguments into the registers that keep them; HMAC's `init`'s arguments. -/
def prologue : List Instr :=
  Hash.saveAt 0 .r10 ++ [mov .r21 .r10, mov .r20 .r6, mov .r22 .r7, mov .r23 .r8, mov .r24 .r9, mov .r25 .r5,
    mov .r5 .r3, mov .r6 .r4, .addi .r3 .r21 F.st0O, .addi .r4 .r21 F.st1O]

/-- `INT (1)`. -/
def loopInit : List Instr := [.li .r12 1, .li .r11 F.intO, .storeRev .w .r12 .r21 .r11]

/-- The key's inner state copied into the working one. -/
def copyW : List Instr := (List.range (F.H.S / 4)).flatMap (cp32 .r21 .r21 F.st0O F.stWO)

/-- `update`'s arguments for the salt: the working state, from a `count` of `B`. -/
def saltArgs : List Instr :=
  [.addi .r3 .r21 F.stWO, .li .r4 F.H.B, mov .r5 .r25, mov .r6 .r20, .addi .r7 .r21 cO]

/-- `update`'s arguments for `INT (i)`: the working state, and the bytes absorbed. -/
def updArgs : List Instr :=
  [.addi .r3 .r21 F.stWO, .addi .r4 .r20 F.H.B, .addi .r5 .r21 F.intO, .li .r6 4, .addi .r7 .r21 cO]

/-- HMAC's `finalize`'s arguments: the working state, the outer state, the
bytes absorbed, `U` and the working space. -/
def finArgs : List Instr :=
  [.addi .r3 .r21 F.stWO, .addi .r4 .r21 F.st1O, .addi .r5 .r20 (F.H.B + 4), .addi .r6 .r21 F.uO,
    .addi .r7 .r21 cO]

/-- `U` copied into `T`. -/
def copyT : List Instr := (List.range (F.H.D / 4)).flatMap (cp32 .r21 .r21 F.uO F.tO)

/-- `iterate`'s arguments: the key's states, `U`, `c - 1`, `T` and the working space. -/
def iterArgs : List Instr :=
  [.addi .r3 .r21 F.st0O, .addi .r4 .r21 F.uO, .subi .r5 .r22 1, .addi .r6 .r21 F.tO, .addi .r7 .r21 cO]

/-- The bytes of `T` the output still needs, `min (r24, D)`, in `r9`. -/
def outLen : Prog isa :=
  .seq (.block [.subi .r12 .r24 F.H.D, .lsr .d .r12 .r12 63, mov .r9 .r24])
    (.ite (.nonzero .d .r12) (.block []) (.block [.li .r9 F.H.D]))

/-- The loop copying `r9` bytes of `T` to `r23`, with `r8` the index. -/
def outLoop : Prog isa :=
  .seq (.block [.li .r8 0])
    (.loop (.block [.add .r11 .r21 .r8, .lbz .r12 .r11 F.tO, .add .r11 .r23 .r8, .stb .r12 .r11 0,
      .addi .r8 .r8 1, .subi .r9 .r9 1]) (.nonzero .d .r9))

/-- Past the bytes written, and the next `INT (i)`. -/
def advance : List Instr :=
  [.add .r23 .r23 .r8, .sub .r24 .r24 .r8, .li .r11 F.intO, .loadRev .w .r12 .r21 .r11, .addi .r12 .r12 1,
    .storeRev .w .r12 .r21 .r11]

/-- One block of the output. -/
def block : Prog isa :=
  .seq (.block (F.copyW ++ F.saltArgs))
  (.seq F.H.callUpd
  (.seq (.block F.updArgs)
  (.seq F.H.callUpd
  (.seq (.block F.finArgs)
  (.seq F.callHf
  (.seq (.block (F.copyT ++ F.iterArgs))
  (.seq F.callIt
  (.seq F.outLen
  (.seq F.outLoop
    (.block F.advance))))))))))

/-- `pbkdf2`, but for saving the link register. -/
def main : Prog isa :=
  .seq (.block F.prologue)
  (.seq F.callHi
  (.seq (.block F.loopInit)
  (.seq (.ite (.zero .d .r24) (.block []) (.loop F.block (.nonzero .d .r24)))
    (.block (Hash.restoreAt 0)))))

/-- PBKDF2 with its working space as an argument. -/
def pbkdf2 : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) F.main (.pop .r0)) (.block [.mtlr .r0]))

end Fns

end VG.Impl.Pbkdf2.Whole.PPC64LE
