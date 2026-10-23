module

public import VerifiedGarbage.Impl.Scrypt.PPC64LE.RoMix

/-!
# scrypt: PPC64LE implementation

`scrypt(password = r3, password_len = r4, salt = r5, salt_len = r6, r = r7,
b = r8, blen = r9, v = r10, vlen, scratch, slen, out, out_len)`, the last
five in the caller's Parameter Save Area, computes scrypt (RFC 7914 §6) with
`N = vlen / r` and `p = blen / r`, as on AArch64
(`Impl/Scrypt/AArch64/Scrypt.lean`):

1. `B = PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` into `b`, by a call of
   `vg_pbkdf2_hmac_sha256_scratch` (or the implementation `pbk` of it given);
2. `vg_scrypt_romix` on each of the `p` blocks of `128 r` bytes of `b`, with
   `v` as `V` and the start of `scratch` (`r + 2` chunks) as its working space;
3. `PBKDF2-HMAC-SHA256 (P, B, 1, out_len)` into `out`, by another call.

Both calls of PBKDF2 use the start of `scratch` as their working space.

The function runs in a frame of `locals` bytes, to which `r30` points
throughout (the callees preserve it): above its 32-byte header, our return
address, our caller's `r30`, the password, its length, `r`, `b`, `blen`, `v`
and the block ROMix works on next. Our stack arguments are above the frame,
from `r30 + locals + 96`.

Only the pointers and the lengths affect timing: the only branch is on the
bytes of `b` left, and every address is in the frame or the caller's
Parameter Save Area (`r30` plus a constant).
-/

@[expose] public section

namespace VG.Impl.Scrypt.PPC64LE.Whole

open VG.PPC64LE

/-! ## The frame -/

/-- The size of the frame. -/
def locals : Nat := 112

def lrOff : Nat := 32
def r30Off : Nat := 40
def pwOff : Nat := 48
def pwlOff : Nat := 56
def rOff : Nat := 64
def bOff : Nat := 72
def blenOff : Nat := 80
def vOff : Nat := 88
def curOff : Nat := 96

/-- Stack argument `i` (`vlen`, `scratch`, `slen`, `out`, `out_len`), in our
caller's Parameter Save Area, above the frame. -/
def argOff (i : Nat) : Nat := locals + 96 + 8 * i

def vlenArg : Nat := 0
def scratchArg : Nat := 1
def outArg : Nat := 3
def outLenArg : Nat := 4

/-- A doubleword of the frame. -/
def fld (r : Reg) (d : Nat) : Instr := .load .d r .r30 d

/-! ## The code -/

/-- Save the return address, our caller's `r30` and the arguments the calls
do not keep, and point `r30` to the frame. -/
def setup : List Instr :=
  [.addSp .r12 0, .mflr .r0, .store .d .r0 .r12 lrOff, .store .d .r30 .r12 r30Off,
   .store .d .r3 .r12 pwOff, .store .d .r4 .r12 pwlOff, .store .d .r7 .r12 rOff, .store .d .r8 .r12 bOff,
   .store .d .r9 .r12 blenOff, .store .d .r10 .r12 vOff, .addi .r30 .r12 0]

/-- The arguments of the first PBKDF2 but those still in their registers
(the password, the salt and `out = b`): `c = 1`, `out_len = 128 blen` and
`scratch`. -/
def pbk1Args : List Instr := [.li .r7 1, .lsl .r9 .r9 7, fld .r10 (argOff scratchArg)]

/-- The first block. -/
def cur0 : List Instr := [fld .r3 bOff, .store .d .r3 .r30 curOff]

/-- `romix(block, r, v, vlen, scratch, r + 2)`. -/
def romixArgs : List Instr :=
  [fld .r3 curOff, fld .r4 rOff, fld .r5 vOff, fld .r6 (argOff vlenArg), fld .r7 (argOff scratchArg),
   .addi .r8 .r4 2]

/-- The next block, `128 r` bytes on, and in `r5` the bytes of `b` after it
(`b + 128 blen` less it). -/
def nextBlock : List Instr :=
  [fld .r3 curOff, fld .r4 rOff, .lsl .r4 .r4 7, .add .r3 .r3 .r4, .store .d .r3 .r30 curOff,
   fld .r5 bOff, fld .r6 blenOff, .lsl .r6 .r6 7, .add .r5 .r5 .r6, .sub .r5 .r5 .r3]

/-- ROMix on each block. -/
def romixLoop : Prog isa :=
  .loop (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix" roMix) (.block nextBlock)))
    (.nonzero .d .r5)

/-- The arguments of the second PBKDF2: the password, `b` as the salt
(`128 blen` bytes), `c = 1`, `out`, `out_len` and `scratch`. -/
def pbk2Args : List Instr :=
  [fld .r3 pwOff, fld .r4 pwlOff, fld .r5 bOff, fld .r6 blenOff, .lsl .r6 .r6 7, .li .r7 1,
   fld .r8 (argOff outArg), fld .r9 (argOff outLenArg), fld .r10 (argOff scratchArg)]

/-- Restore the return address and our caller's `r30`. -/
def restore : List Instr := [fld .r0 lrOff, .mtlr .r0, fld .r30 r30Off]

/-- A call of the implementation `pbk` of PBKDF2-HMAC-SHA256, named
`pbkName`, after the moves `args` of its arguments. -/
def pbkCall (pbkName : String) (pbk : Prog isa) (args : List Instr) : Prog isa :=
  .seq (.block args) (.call pbkName pbk)

/-- The frame's body, with the implementation `pbk` of PBKDF2-HMAC-SHA256,
named `pbkName`. -/
def scryptBody (pbkName : String) (pbk : Prog isa) : Prog isa :=
  .seq (.block setup)
    (.seq (pbkCall pbkName pbk pbk1Args)
      (.seq (.block cur0) (.seq romixLoop (.seq (pbkCall pbkName pbk pbk2Args) (.block restore)))))

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2-HMAC-SHA256,
named `pbkName`. -/
def scrypt (pbkName : String) (pbk : Prog isa) : Prog isa :=
  .frame (.alloc locals) (scryptBody pbkName pbk) (.free locals)

end VG.Impl.Scrypt.PPC64LE.Whole
