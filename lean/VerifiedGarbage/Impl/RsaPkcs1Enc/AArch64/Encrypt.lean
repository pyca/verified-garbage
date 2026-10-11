module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64

`vg_rsa_pkcs1_encrypt(out = x0, out_len = x1, n = x2, n_len = x3, e = x4,
e_len = x5, msg = x6, msg_len = x7, ps, ps_len, scratch, scratch_len)`, the
last four on the stack, as on x86-64 (`Impl/RsaPkcs1Enc/X86_64/Encrypt.lean`):
it builds the encoded message `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` in its frame
and calls `vg_rsa_public_checked` (`pub`, by its name `pubName`) on it, which
checks `n` and `e` and writes `EM^e mod n` or zeros to `out`:

1. `out` and `n_len`, which the call may change, are kept in slots of the
   frame, and the call's stack arguments (`scratch`, `scratch_len`) are
   written at `sp`. `EM` starts with `0x00 ‖ 0x02`.
2. `PS` is copied after them, byte by byte, and `x14` collects, without
   branches, whether any byte is zero: all ones if one is, zero if not
   (`psLoop`). The length of `PS` is at least 8 (a precondition).
3. The separator `0x00` follows, and `M` after it (`msgCopy`, skipped if
   `msg_len` is 0: a branch on a public length).
4. The call, whose first six arguments are still ours: only `input` and
   `input_len` (`EM` and `n_len`) are set.
5. If `PS` had a zero byte, `out` is masked to zeros and the result to 0
   (`maskLoop`), without branches; the loop also overwrites `EM` with
   zeros.

The function runs in two frames: one saving our return address `x30`, and in
it one of `frameBytes` bytes holding, from `sp`, the call's stack arguments,
the slots from `oOut`, and `EM` (up to 1024 bytes) from `oEM`. Our own stack
arguments are above both frames, from `sp + frameBytes + 16`. The call uses
the stack below the frames.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

open VG VG.AArch64

/-- The size of the inner frame. -/
def frameBytes : Nat := 1072

/-- The slots: `out`, `n_len`, and whether `PS` has a zero byte. -/
def oOut : Nat := 16
def oK : Nat := 24
def oZ : Nat := 32
/-- `EM`, up to 1024 bytes. -/
def oEM : Nat := 40

/-- Our stack argument `j` (from 0), from `sp` in the frames. -/
def arg (j : Nat) : Nat := frameBytes + 16 + 8 * j

/-- The call's stack arguments (`scratch` and `scratch_len`) into `x10` and
`x11`, and the frame's base into `x9`. -/
def loadArgs : List Instr := [.ldrSp .x10 (arg 2), .ldrSp .x11 (arg 3), .addSp .x9 0]

/-- Those, `out` and `n_len` to the frame. -/
def saves : List Instr := [.str .x .x10 .x9 0, .str .x .x11 .x9 8, .str .x .x0 .x9 oOut, .str .x .x3 .x9 oK]

/-- The first two bytes of `EM`, and `PS`'s copy's registers: `PS` in `x11`,
its length in `x12`, the place of its copy in `x13`, the collected zero test
`x14` zero and the constant 1 in `x15`. -/
def emStart : List Instr :=
  [.movz .x .x10 0 0, .strb .x10 .x9 oEM, .movz .x .x10 2 0, .strb .x10 .x9 (oEM + 1),
    .ldrSp .x11 (arg 0), .ldrSp .x12 (arg 1), .addImm .x .x13 .x9 (oEM + 2),
    .movz .x .x14 0 0, .movz .x .x15 1 0]

def setup : List Instr := loadArgs ++ (saves ++ emStart)

/-- One byte of `PS`: copied to `EM`, and `x14` all ones if it is zero (the
borrow of `byte - 1`). -/
def psBody : List Instr :=
  [.ldrb .x10 .x11 0, .strb .x10 .x13 0, .subs .x .x16 .x10 .x15, .sbc .x .x16 .x10 .x10,
    .logic .orr .x .x14 .x14 .x16, .addImm .x .x11 .x11 1, .addImm .x .x13 .x13 1,
    .subImm .x .x12 .x12 1]

def psLoop : Prog isa := .loop (.block psBody) (.nonzero .x .x12)

/-- The separator after `PS`, the zero test to its slot; `x13` is then where
`M` goes. -/
def sep : List Instr :=
  [.movz .x .x10 0 0, .strb .x10 .x13 0, .addImm .x .x13 .x13 1, .addSp .x9 0, .str .x .x14 .x9 oZ]

/-- One byte of `M` (at `x6`, `x7` bytes left) to `x13`. -/
def msgBody : List Instr :=
  [.ldrb .x10 .x6 0, .strb .x10 .x13 0, .addImm .x .x6 .x6 1, .addImm .x .x13 .x13 1,
    .subImm .x .x7 .x7 1]

def msgLoop : Prog isa := .loop (.block msgBody) (.nonzero .x .x7)

/-- `M`, unless it is empty. -/
def msgCopy : Prog isa := .ite (.nonzero .x .x7) msgLoop (.block [])

/-- The call's `input` and `input_len`: `EM` and `n_len`. -/
def callArgs : List Instr := [.addSp .x6 oEM, .logic .orr .x .x7 .x3 .x3]

/-- The result masked by the zero test `x14` into `x0`; `out` into `x11`,
`n_len` into `x12`, `EM` into `x13`, zero into `x15`. -/
def maskArgs : List Instr :=
  [.ldrSp .x14 oZ, .bicRor .x .x0 .x0 .x14 0, .ldrSp .x11 oOut, .ldrSp .x12 oK, .addSp .x13 oEM,
    .movz .x .x15 0 0]

/-- `out[i] &= ~x14` and `EM[i] := 0` for each byte. -/
def maskBody : List Instr :=
  [.ldrb .x10 .x11 0, .bicRor .x .x10 .x10 .x14 0, .strb .x10 .x11 0, .strb .x15 .x13 0,
    .addImm .x .x11 .x11 1, .addImm .x .x13 .x13 1, .subImm .x .x12 .x12 1]

def maskLoop : Prog isa := .loop (.block maskBody) (.nonzero .x .x12)

/-- The inner frame's body. -/
def body (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block setup) (.seq psLoop (.seq (.block sep) (.seq msgCopy (.seq (.block callArgs)
    (.seq (.call pubName pub) (.seq (.block maskArgs) maskLoop))))))

/-- `vg_rsa_pkcs1_encrypt`, calling `vg_rsa_public_checked`'s code `pub` by
its name. -/
def code (pubName : String) (pub : Prog isa) : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes) (body pubName pub) (.free frameBytes)) (.pop .x30)

end VG.Impl.RsaPkcs1Enc.AArch64.Encrypt
