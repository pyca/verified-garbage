module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Precomputed

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on PPC64LE

`vg_rsa_pkcs1_encrypt_random(out = r3, out_len = r4, tape = r5, n = r6,
n_len = r7, e = r8, e_len = r9, msg = r10, msg_len, rand, rand_len,
scratch, scratch_len, pre, pre_len)`, the last seven on the stack (ELFv2
ABI §2.2.3.3, the Parameter Save Area at `sp + 96`). It draws the padding
string `PS` (`psLen = n_len - msg_len - 3` octets) into its frame and, once
it has all of it, calls `vg_rsa_pkcs1_encrypt_precomputed` with it:

1. The caller's `r28`–`r31` and our return address are saved; `out`,
   `tape`, `n_len` and `psLen` are kept in `r31`–`r28` (`setup`); `n`, `e`,
   `e_len` and `msg` stay in `r6`, `r8`, `r9` and `r10`.
2. The scan (`scan`, skipped if `rand_len` is 0): octet `r4` of `rand`
   (`r3`) in turn, in `r0`, kept at the end of `PS` (`r7`, index `r5`) unless
   it is zero, until `PS` is full or `rand` (`r11` octets) ends. It branches
   on whether each octet is zero, which the contract makes public, and on the
   two indices, which follow from it.
3. With `PS` full (`accept`): `tape` is `[r4, 0]`, the call's arguments are
   those of `vg_rsa_pkcs1_encrypt_precomputed` with `PS` the frame's, the
   status is `2 - r` from its result `r` (1 for 1, 2 for 0), and `PS` is
   wiped.
4. Otherwise (`reject`, with `rand_len`, the index `r4`, kept in `r10`): `out`
   is zeroed, the `r5` octets drawn are wiped, and with the budget
   `cap = psLen + 128`: if `rand_len` is `cap`, status 3
   and `tape` is `[rand_len, 0]`; else status 0 and `tape` is
   `[0, min(cap, psLen + rand_len - r5)]`, more than `rand_len` as
   `r5 < psLen`.

The frame (`frameBytes`): at `sp + 96`, the call's six stack arguments;
from `oSave`, the caller's `r28`–`r31`, then our return address (`oLr`);
from `oBuf`, `PS`, up to 1024 bytes. Our own stack arguments are at
`sp + frameBytes + 96 + 8 i` (`arg i`). The frame is addressed through `r12`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.PPC64LE.Random

open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)
open VG.Impl.RsaPkcs1Sig.PPC64LE (fillLoop)

/-- The size of the frame. -/
def frameBytes : Nat := 1216

/-- The caller's `r28`–`r31`, our return address and `PS`. -/
def oSave : Nat := 144
def oLr : Nat := 176
def oBuf : Nat := 192

/-- Our stack argument `i` (from 0), in the frame. -/
def arg (i : Nat) : Nat := frameBytes + 96 + 8 * i

/-- `r12 := r1`; our caller's `r28`–`r31` and our return address into the
frame. -/
def save : List Instr :=
  [.addSp .r12 0, .store .d .r28 .r12 oSave, .store .d .r29 .r12 (oSave + 8), .store .d .r30 .r12 (oSave + 16),
    .store .d .r31 .r12 (oSave + 24), .mflr .r0, .store .d .r0 .r12 oLr]

/-- Our caller's `r28`–`r31` and our return address back from the frame. -/
def restore : List Instr :=
  [.addSp .r12 0, .load .d .r0 .r12 oLr, .mtlr .r0, .load .d .r28 .r12 oSave, .load .d .r29 .r12 (oSave + 8),
    .load .d .r30 .r12 (oSave + 16), .load .d .r31 .r12 (oSave + 24)]

/-- The saves; `out`, `tape`, `n_len`, `psLen` into `r31`–`r28`; and the
scan's registers: `rand` in `r3`, `rand_len` in `r11`, `PS` in `r7`, the
indices `r4` and `r5` zero. -/
def setup : List Instr :=
  save ++ [mov .r31 .r3, mov .r30 .r5, mov .r29 .r7, .load .d .r0 .r12 (arg 0), .sub .r28 .r7 .r0,
    .subi .r28 .r28 3, .load .d .r3 .r12 (arg 1), .load .d .r11 .r12 (arg 2), .addi .r7 .r12 oBuf,
    .li .r4 0, .li .r5 0]

/-- The octet `r4` of `rand` into `r0`, and `r4` past it. -/
def load : List Instr := [.add .r12 .r3 .r4, .lbz .r0 .r12 0, .addi .r4 .r4 1]

/-- A nonzero octet, kept at the end of `PS`. -/
def keep : List Instr := [.add .r12 .r7 .r5, .stb .r0 .r12 0, .addi .r5 .r5 1]

/-- Whether to go on: `r12` nonzero unless `PS` is full or `rand` has ended. -/
def more : Prog isa :=
  .seq (.block [.sub .r12 .r28 .r5]) (.ite (.nonzero .d .r12) (.block [.sub .r12 .r11 .r4]) (.block []))

/-- One octet of the scan. -/
def step : Prog isa := .seq (.block load) (.seq (.ite (.nonzero .d .r0) (.block keep) (.block [])) more)

/-- The scan, unless `rand` is empty. -/
def scan : Prog isa := .ite (.nonzero .d .r11) (.loop step (.nonzero .d .r12)) (.block [])

/-- `tape` is `[r4, 0]`; the call's stack arguments: `PS`, `psLen`,
`scratch`, `scratch_len`, `pre` and `pre_len`. -/
def stackArgs : List Instr :=
  [.store .d .r4 .r30 0, .li .r0 0, .store .d .r0 .r30 8, .addSp .r12 0, .store .d .r7 .r12 96,
    .store .d .r28 .r12 104, .load .d .r0 .r12 (arg 3), .store .d .r0 .r12 112, .load .d .r0 .r12 (arg 4),
    .store .d .r0 .r12 120, .load .d .r0 .r12 (arg 5), .store .d .r0 .r12 128, .load .d .r0 .r12 (arg 6),
    .store .d .r0 .r12 136]

/-- The call's register arguments: `out`, `n_len`, `n`, `n_len`, `e`,
`e_len`, `msg` and `msg_len`. -/
def regArgs : List Instr :=
  [mov .r3 .r31, mov .r4 .r29, mov .r5 .r6, mov .r6 .r29, mov .r7 .r8, mov .r8 .r9, mov .r9 .r10,
    .load .d .r10 .r12 (arg 0)]

/-- `vg_rsa_pkcs1_encrypt_precomputed`. -/
def encCall : Prog isa := .call "vg_rsa_pkcs1_encrypt_precomputed" Precomputed.code

/-- The status `2 - r3` into `r5`, and `fillLoop`'s registers to wipe `PS`:
its place, `psLen` and the zero byte. -/
def status : List Instr :=
  [.li .r5 2, .sub .r5 .r5 .r3, .addSp .r12 0, .addi .r4 .r12 oBuf, mov .r11 .r28, .li .r0 0]

/-- `PS` full: the call, the status and the wipe. -/
def accept : Prog isa :=
  .seq (.block (stackArgs ++ regArgs)) (.seq encCall (.seq (.block status) (.seq fillLoop (.block [mov .r3 .r5]))))

/-- `rand_len` (the index, all of the tape read) kept in `r10`; `out` zeroed:
`fillLoop`'s registers. -/
def zeroArgs : List Instr := [mov .r10 .r4, mov .r4 .r31, mov .r11 .r29, .li .r0 0]

/-- The drawn octets' wipe: its registers. -/
def wipeArgs : List Instr := [.addSp .r12 0, .addi .r4 .r12 oBuf, mov .r11 .r5]

/-- The budget into `r12`, and `cap - rand_len` into `r0`. -/
def budget : List Instr := [.addi .r12 .r28 128, .sub .r0 .r12 .r10]

/-- Exhausted: `tape` is `[rand_len, 0]`, status 3. -/
def exhausted : List Instr := [.store .d .r10 .r30 0, .li .r0 0, .store .d .r0 .r30 8, .li .r3 3]

/-- More entropy: `tape[0] := 0`, and in `r4` whether
`rand_len - drawn < 129`, so that `psLen + rand_len - drawn ≤ cap`. -/
def reqHead : List Instr := [.li .r0 0, .store .d .r0 .r30 0, .sub .r4 .r10 .r5, .subi .r4 .r4 129, .lsr .d .r4 .r4 63]

/-- `tape[1] := min(cap, psLen + rand_len - drawn)`, status 0. -/
def request : Prog isa :=
  .seq (.block reqHead) (.seq (.ite (.nonzero .d .r4) (.block [.add .r0 .r28 .r10, .sub .r0 .r0 .r5])
    (.block [mov .r0 .r12])) (.block [.store .d .r0 .r30 8, .li .r3 0]))

/-- `PS` not full. -/
def reject : Prog isa :=
  .seq (.block zeroArgs) (.seq fillLoop (.seq (.block wipeArgs) (.seq (.ite (.nonzero .d .r11) fillLoop (.block []))
    (.seq (.block budget) (.ite (.zero .d .r0) (.block exhausted) request)))))

/-- The body of the frame. -/
def body : Prog isa :=
  .seq (.block setup) (.seq scan (.seq (.block [.sub .r12 .r28 .r5])
    (.seq (.ite (.zero .d .r12) accept reject) (.block restore))))

/-- `vg_rsa_pkcs1_encrypt_random`. -/
def code : Prog isa := .frame (.alloc frameBytes) body (.free frameBytes)

end VG.Impl.RsaPkcs1Enc.PPC64LE.Random
