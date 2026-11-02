module

public import VerifiedGarbage.Impl.Scrypt.RISCV64.RoMix

/-!
# scrypt: RISC-V implementation

`scrypt(password = a0, password_len = a1, salt = a2, salt_len = a3, r = a4,
b = a5, blen = a6, v = a7, vlen, scratch, slen, out, out_len)`, the last
five on the caller's stack, computes scrypt (RFC 7914 §6) with
`N = vlen / r` and `p = blen / r`, as on PPC64LE
(`Impl/Scrypt/PPC64LE/Scrypt.lean`):

1. `B = PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` into `b`, by a call of
   `vg_pbkdf2_hmac_sha256` (or the implementation `pbk` of it given), which
   works on the stack below our frame;
2. scryptROMix on each of the `p` blocks of `128 r` bytes of `b`, with `v`
   as `V` and the start of `scratch` as `T`: `vg_scrypt_romix` if `b`, `v`
   and `scratch` are all multiples of 8, else `vg_scrypt_romix_bytes` (the
   choice is made once);
3. `PBKDF2-HMAC-SHA256 (P, B, 1, out_len)` into `out`, by another call.

The function runs in a frame of `locals` bytes, to which `s3` points
throughout (the callees preserve it): our return address, our caller's
`s3`, the password, its length, `r`, `b`, `blen`, `v` and the block ROMix
works on next. Our stack arguments are above the frame, from
`s3 + locals`.

Only the pointers and the lengths affect timing: the branches are on the
pointers' low bits and on the bytes of `b` left, and every address is in
the frame or our stack arguments (`s3` plus a constant).
-/

@[expose] public section

namespace VG.Impl.Scrypt.RISCV64.Whole

open VG.RISCV64
open VG.Impl.Scrypt.RISCV64 (mov roMix roMixName)

/-! ## The frame -/

/-- The size of the frame. -/
def locals : Nat := 80

def raOff : Nat := 0
def s3Off : Nat := 8
def pwOff : Nat := 16
def pwlOff : Nat := 24
def rOff : Nat := 32
def bOff : Nat := 40
def blenOff : Nat := 48
def vOff : Nat := 56
def curOff : Nat := 64

/-- Stack argument `i` (`vlen`, `scratch`, `slen`, `out`, `out_len`), on our
caller's stack, above the frame. -/
def argOff (i : Nat) : Nat := locals + 8 * i

def vlenArg : Nat := 0
def scratchArg : Nat := 1
def outArg : Nat := 3
def outLenArg : Nat := 4

/-- A doubleword of the frame. -/
def fld (r : Reg) (d : Nat) : Instr := .load .d r .s3 d

/-! ## The code -/

/-- Save the return address, our caller's `s3` and the arguments the calls
do not keep, and point `s3` to the frame. -/
def setup : List Instr :=
  [.addSp .t0 0, .store .d .ra .t0 raOff, .store .d .s3 .t0 s3Off,
   .store .d .a0 .t0 pwOff, .store .d .a1 .t0 pwlOff, .store .d .a4 .t0 rOff, .store .d .a5 .t0 bOff,
   .store .d .a6 .t0 blenOff, .store .d .a7 .t0 vOff, mov .s3 .t0]

/-- The arguments of the first PBKDF2 but those still in their registers
(the password, the salt and `out = b`): `c = 1` and `out_len = 128 blen`. -/
def pbk1Args : List Instr := [.li .a4 1, .shift .sll .d .a6 .a6 7]

/-- The first block. -/
def cur0 : List Instr := [fld .a0 bOff, .store .d .a0 .s3 curOff]

/-- `t0 ←` the low three bits of `b | v | scratch`. -/
def alignBits : List Instr :=
  [fld .t0 bOff, fld .t1 vOff, .logic .or .t0 .t0 .t1, fld .t1 (argOff scratchArg),
   .logic .or .t0 .t0 .t1, .logicImm .and .t0 .t0 7]

/-- `romix(block, r, v, vlen, scratch)`. -/
def romixArgs : List Instr :=
  [fld .a0 curOff, fld .a1 rOff, fld .a2 vOff, fld .a3 (argOff vlenArg), fld .a4 (argOff scratchArg)]

/-- The next block, `128 r` bytes on, and in `t0` the bytes of `b` after it
(`b + 128 blen` less it). -/
def nextBlock : List Instr :=
  [fld .a0 curOff, fld .a1 rOff, .shift .sll .d .a1 .a1 7, .add .a0 .a0 .a1, .store .d .a0 .s3 curOff,
   fld .t0 bOff, fld .t1 blenOff, .shift .sll .d .t1 .t1 7, .add .t0 .t0 .t1, .sub .t0 .t0 .a0]

/-- ROMix on each block. -/
def romixLoop (wide : Bool) : Prog isa :=
  .loop (.seq (.block romixArgs) (.seq (.call (roMixName wide) (roMix wide)) (.block nextBlock)))
    (.nonzero .t0)

/-- ROMix on each block, by doublewords if every pointer allows it. -/
def romixAll : Prog isa :=
  .seq (.block alignBits) (.ite (.zero .t0) (romixLoop true) (romixLoop false))

/-- The arguments of the second PBKDF2: the password, `b` as the salt
(`128 blen` bytes), `c = 1`, `out` and `out_len`. -/
def pbk2Args : List Instr :=
  [fld .a0 pwOff, fld .a1 pwlOff, fld .a2 bOff, fld .a3 blenOff, .shift .sll .d .a3 .a3 7, .li .a4 1,
   fld .a5 (argOff outArg), fld .a6 (argOff outLenArg)]

/-- Restore the return address and our caller's `s3`. -/
def restore : List Instr := [fld .ra raOff, fld .s3 s3Off]

/-- A call of the implementation `pbk` of PBKDF2-HMAC-SHA256, named
`pbkName`, after the moves `args` of its arguments. -/
def pbkCall (pbkName : String) (pbk : Prog isa) (args : List Instr) : Prog isa :=
  .seq (.block args) (.call pbkName pbk)

/-- The frame's body, with the implementation `pbk` of PBKDF2-HMAC-SHA256,
named `pbkName`. -/
def scryptBody (pbkName : String) (pbk : Prog isa) : Prog isa :=
  .seq (.block setup)
    (.seq (pbkCall pbkName pbk pbk1Args)
      (.seq (.block cur0) (.seq romixAll (.seq (pbkCall pbkName pbk pbk2Args) (.block restore)))))

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2-HMAC-SHA256,
named `pbkName`. -/
def scrypt (pbkName : String) (pbk : Prog isa) : Prog isa :=
  .frame (.alloc locals) (scryptBody pbkName pbk) (.free locals)

end VG.Impl.Scrypt.RISCV64.Whole
