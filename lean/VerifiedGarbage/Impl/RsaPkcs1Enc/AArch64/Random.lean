module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64

`vg_rsa_pkcs1_encrypt_random(out = x0, out_len = x1, tape = x2, n = x3,
n_len = x4, e = x5, e_len = x6, msg = x7, msg_len, rand, rand_len, scratch,
scratch_len, pre, pre_len)`, the last seven on the stack, as on x86-64
(`Impl/RsaPkcs1Enc/X86_64/Random.lean`): it draws the padding string `PS`
(`psLen = n_len - msg_len - 3` octets) into its frame and, once it has all
of it, calls `vg_rsa_pkcs1_encrypt_precomputed` (`enc`, by its name
`encName`) with it. The argument registers `x0`–`x7` are kept until the
call:

1. `setup`: `psLen` into `x15` and its slot, `rand` into `x11`, `rand_len`
   (the octets left) into `x12`, the end of `PS` into `x14`, and the octets
   still to draw into `x16`.
2. The scan (`scan`, skipped if `rand_len` is 0): each octet of `rand` in
   turn, in `x17`, kept at the end of `PS` unless it is zero, until `PS` is
   full (`x16` zero) or `rand` ends (`x12` zero), the loop going on while
   their product `x9` is not zero. It branches on whether each octet is
   zero, which the contract makes public.
3. With `PS` full (`accept`): `tape` is `[rand_len - x12, 0]`, the call's
   stack arguments go at `sp` and its registers are ours shifted down one
   (`x7` is `msg_len`), loaded before anything is stored (`callArgs`); the
   status is `2 - w0`, and `PS` is wiped.
4. Otherwise (`reject`): `out` is zeroed, `PS`'s area is wiped, and with
   the budget `cap = psLen + 128`: if `rand_len ≥ cap`, status 3 and `tape`
   is `[rand_len, 0]`; else status 0 and `tape` is
   `[0, min(cap, psLen + rand_len - drawn)]`, chosen with no branch
   (`outcome`).

The wipes clear all 1024 bytes of `PS`'s area, so that no loop's length
depends on more than the public data.

The function runs in two frames: one saving `x30`, and in it one of
`frameBytes` bytes holding, from `sp`, the call's six stack arguments, the
slot `oPs`, and `PS` (up to 1024 bytes) from `oBuf`. Our own stack
arguments are above both frames, from `sp + frameBytes + 16`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.AArch64.Random

open VG VG.AArch64

/-- The size of the inner frame. -/
def frameBytes : Nat := 1088

/-- The slot of `psLen`, and `PS`. -/
def oPs : Nat := 48
def oBuf : Nat := 64

/-- Our stack argument `j` (from 0), from `sp` in the frames. -/
def arg (j : Nat) : Nat := frameBytes + 16 + 8 * j

def setup : List Instr :=
  [.ldrSp .x9 (arg 0), .ldrSp .x11 (arg 1), .ldrSp .x12 (arg 2), .sub .x .x15 .x4 .x9,
    .subImm .x .x15 .x15 3, .strSp .x15 oPs, .addSp .x14 oBuf, .logic .orr .x .x16 .x15 .x15]

/-- The octet at `x11` into `x17`, `x11` past it, one octet fewer left. -/
def load : List Instr := [.ldrb .x17 .x11 0, .addImm .x .x11 .x11 1, .subImm .x .x12 .x12 1]

/-- A nonzero octet, kept at the end of `PS`. -/
def keep : List Instr := [.strb .x17 .x14 0, .addImm .x .x14 .x14 1, .subImm .x .x16 .x16 1]

/-- One octet of the scan; `x9` zero once `PS` is full or `rand` has ended. -/
def step : Prog isa :=
  .seq (.block load) (.seq (.ite (.zero .x .x17) (.block []) (.block keep)) (.block [.mul .x .x9 .x12 .x16]))

/-- The scan, unless `rand` is empty. -/
def scan : Prog isa := .ite (.nonzero .x .x12) (.loop step (.nonzero .x .x9)) (.block [])

/-- The call's arguments, all loads first: `tape` is `[rand_len - x12, 0]`;
the call's stack arguments `PS`, `psLen`, `scratch`, `scratch_len`, `pre`,
`pre_len` at `sp`; and its registers ours shifted down one, `x7` being
`msg_len`. -/
def callArgs : List Instr :=
  [.ldrSp .x9 (arg 2), .sub .x .x9 .x9 .x12, .ldrSp .x10 (arg 3), .ldrSp .x11 (arg 4), .ldrSp .x13 (arg 5),
    .ldrSp .x14 (arg 6), .ldrSp .x8 (arg 0), .addSp .x16 oBuf, .movz .x .x17 0 0,
    .str .x .x9 .x2 0, .str .x .x17 .x2 8, .strSp .x16 0, .strSp .x15 8, .strSp .x10 16, .strSp .x11 24,
    .strSp .x13 32, .strSp .x14 40,
    .logic .orr .x .x2 .x3 .x3, .logic .orr .x .x3 .x4 .x4, .logic .orr .x .x4 .x5 .x5,
    .logic .orr .x .x5 .x6 .x6, .logic .orr .x .x6 .x7 .x7, .logic .orr .x .x7 .x8 .x8]

/-- The status `2 - w0`, and the wipe's registers: the 1024 bytes of `PS`'s
area in `x12`, `PS` in `x13`, zero in `x14`. -/
def status : List Instr :=
  [.movz .x .x9 2 0, .sub .w .x0 .x9 .x0, .movz .x .x12 1024 0, .addSp .x13 oBuf, .movz .x .x14 0 0]

/-- `x12` zero bytes from `x13` (at least one), from `x14`. -/
def wipe : Prog isa :=
  .loop (.block [.strb .x14 .x13 0, .addImm .x .x13 .x13 1, .subImm .x .x12 .x12 1]) (.nonzero .x .x12)

/-- `PS` full: the call, and the status. -/
def accept (encName : String) (enc : Prog isa) : Prog isa :=
  .seq (.block callArgs) (.seq (.call encName enc) (.seq (.block status) wipe))

/-- `out` zeroed (`n_len` bytes, at least one), from `x13`. -/
def zeroOut : Prog isa :=
  .seq (.block [.logic .orr .x .x9 .x0 .x0, .logic .orr .x .x10 .x4 .x4, .movz .x .x13 0 0])
    (.loop (.block [.strb .x13 .x9 0, .addImm .x .x9 .x9 1, .subImm .x .x10 .x10 1]) (.nonzero .x .x10))

/-- `PS`'s area wiped, the octets drawn among it. -/
def wipeDrawn : Prog isa :=
  .seq (.block [.movz .x .x10 1024 0, .addSp .x9 oBuf])
    (.loop (.block [.strb .x13 .x9 0, .addImm .x .x9 .x9 1, .subImm .x .x10 .x10 1]) (.nonzero .x .x10))

/-- The outcome, with no branch: with the budget `cap = psLen + 128`
(`x11`), `rand_len` (`x12`) and the octets drawn `psLen - x16` (`x10`), if
`rand_len ≥ cap` (exhausted), `tape` is `[rand_len, 0]` and the status 3;
otherwise `tape` is `[0, min(cap, psLen + rand_len - drawn)]` and the
status 0. -/
def outcome : List Instr :=
  [.addImm .x .x11 .x15 128, .ldrSp .x12 (arg 2), .sub .x .x10 .x15 .x16, .add .x .x9 .x15 .x12,
    .sub .x .x9 .x9 .x10, .subs .x .x17 .x11 .x9, .cselc .x .x9 .x11 .x9 .lo, .subs .x .x17 .x12 .x11,
    .movz .x .x13 0 0, .cselc .x .x14 .x12 .x13 .hs, .cselc .x .x9 .x13 .x9 .hs, .movz .x .x10 3 0,
    .cselc .x .x0 .x10 .x13 .hs, .str .x .x14 .x2 0, .str .x .x9 .x2 8]

/-- `PS` not full. -/
def reject : Prog isa := .seq zeroOut (.seq wipeDrawn (.block outcome))

/-- The inner frame's body. -/
def body (encName : String) (enc : Prog isa) : Prog isa :=
  .seq (.block setup) (.seq scan (.ite (.zero .x .x16) (accept encName enc) reject))

/-- `vg_rsa_pkcs1_encrypt_random`, calling an implementation of
`vg_rsa_pkcs1_encrypt_precomputed`'s code `enc` by its name. -/
def code (encName : String) (enc : Prog isa) : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes) (body encName enc) (.free frameBytes)) (.pop .x30)

end VG.Impl.RsaPkcs1Enc.AArch64.Random
