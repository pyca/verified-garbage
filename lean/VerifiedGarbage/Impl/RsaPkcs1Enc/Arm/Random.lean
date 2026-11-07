module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Wrap
public import VerifiedGarbage.Impl.Bignum.Arm.MaskBytes

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on ARMv7

`vg_rsa_pkcs1_encrypt_random(out = r0, out_len = r1, tape = r2, n = r3,
n_len, e, e_len, msg, msg_len, rand, rand_len, scratch, scratch_len, pre,
pre_len)`, the last eleven on the stack. It draws the padding string `PS`
(`psLen = n_len - msg_len - 3` octets) into its frame and, once it has all of
it, calls `vg_rsa_pkcs1_encrypt_precomputed` (`enc`, by its name `encName`)
with it:

1. `start`: `rand` in `r1`, `rand_len` in `r8`, `psLen` in `r3`, `PS` in
   `r0`, the index `r4` and the count `r5` zero; then whether `rand` is empty.
2. The scan (`scan`, skipped if `rand_len` is 0): each octet of `rand` in
   turn, in `r6`, kept at `r0` (and `r0` and the count `r5` past it) unless it
   is zero, until `PS` is full or `rand` ends. It branches on whether each
   octet is zero, which the contract makes public, and on the count and the
   index, which follow from it.
3. With `PS` full (`accept`): `tape` is `[i, 0]` (`r7` the tape, two words
   each), the call's arguments (`PS` the frame's), the call, the status
   `2 - r` in `r4`, `PS` wiped (`maskBytes` with a zero mask).
4. Otherwise (`reject`): `out` zeroed and the `r5` octets drawn wiped
   (`maskBytes`), and with the budget `cap = psLen + 128`: if `rand_len = cap`
   (the contract bounds `rand_len` by `cap`), status 3 and `tape` is
   `[rand_len, 0]`; else status 0 and `tape` is
   `[0, min(cap, psLen + rand_len - r5)]`, the minimum without a branch.

The frame (`Impl/RsaPkcs1Sig/Arm/Wrap.lean`) holds the call's ten stack
arguments from its base and `PS` (up to 1024 bytes) at `oBuf`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.Arm.Random

open VG VG.Arm
open VG.Impl.RsaPkcs1Sig.Arm (wrap argOff)

/-- The size of the inner frame. -/
def frameBytes : Nat := 1088

/-- `PS`. -/
def oBuf : Nat := 40

/-- Argument `j` (from 0). -/
def arg (j : Nat) : Nat := argOff frameBytes j

/-- The scan's registers. -/
def start : List Instr :=
  [.addSp .r12 0, .ldrSp .r1 (arg 9), .ldrSp .r8 (arg 10), .ldrSp .r3 (arg 4), .ldrSp .r4 (arg 8),
    .dp .sub .r3 .r3 (.reg .r4), .dp .sub .r3 .r3 (.imm 3), .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oBuf)),
    .mov .r4 (.imm 0), .mov .r5 (.imm 0)]

/-- The octet at `r1` into `r6`, `r1` and the index `r4` past it; Z set if it is zero. -/
def load : List Instr :=
  [.ldrb .r6 .r1 0, .dp .add .r1 .r1 (.imm 1), .dp .add .r4 .r4 (.imm 1), .cmp .r6 (.imm 0)]

/-- A nonzero octet, kept at `r0`. -/
def keep : List Instr := [.strb .r6 .r0 0, .dp .add .r0 .r0 (.imm 1), .dp .add .r5 .r5 (.imm 1)]

/-- Z clear unless `PS` is full or `rand` has ended. -/
def more : Prog isa :=
  .seq (.block [.cmp .r5 (.reg .r3)]) (.ite .eq (.block [.cmp .r5 (.reg .r5)]) (.block [.cmp .r4 (.reg .r8)]))

def step : Prog isa := .seq (.block load) (.seq (.ite .ne (.block keep) (.block [])) more)

/-- The scan, unless `rand` is empty. -/
def scan : Prog isa := .seq (.block [.cmp .r8 (.imm 0)]) (.ite .ne (.loop step .ne) (.block []))

/-- `tape` is `[i, 0]`, `i` in `r4`. -/
def tapeLoad : List Instr := [.ldrSp .r7 (arg 2)]
def tapeStore : List Instr :=
  [.mov .r6 (.imm 0), .str .r4 .r7 0, .str .r6 .r7 4, .str .r6 .r7 8, .str .r6 .r7 12]

/-- The call's stack arguments, then its registers: `out`, `n_len`, `n`, `n_len`. -/
def callArgs : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 5), .str .r0 .r12 0, .ldrSp .r0 (arg 6), .str .r0 .r12 4,
    .ldrSp .r0 (arg 7), .str .r0 .r12 8, .ldrSp .r0 (arg 8), .str .r0 .r12 12,
    .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oBuf)), .str .r0 .r12 16, .str .r3 .r12 20,
    .ldrSp .r0 (arg 11), .str .r0 .r12 24, .ldrSp .r0 (arg 12), .str .r0 .r12 28,
    .ldrSp .r0 (arg 13), .str .r0 .r12 32, .ldrSp .r0 (arg 14), .str .r0 .r12 36,
    .ldrSp .r0 (arg 0), .ldrSp .r1 (arg 4), .ldrSp .r2 (arg 3), .ldrSp .r3 (arg 4)]

/-- The status `2 - r`. -/
def status : List Instr := [.mov .r4 (.imm 2), .dp .sub .r4 .r4 (.reg .r0)]

/-- `PS` and its length for `maskBytes` with a zero mask. -/
def wipeArgs : List Instr :=
  [.addSp .r12 0, .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oBuf)), .ldrSp .r1 (arg 4), .ldrSp .r2 (arg 8),
    .dp .sub .lr .r1 (.reg .r2), .dp .sub .lr .lr (.imm 3), .mov .r2 (.imm 0)]

def accept (encName : String) (enc : Prog isa) : Prog isa :=
  .seq (.block tapeLoad) (.seq (.block tapeStore) (.seq (.block callArgs) (.seq (.call encName enc)
    (.seq (.block status) (.seq (.block wipeArgs) (.seq Bignum.Arm.maskBytes (.block [.mov .r0 (.reg .r4)])))))))

/-- `out` and `n_len` for `maskBytes` with a zero mask. -/
def zeroArgs : List Instr := [.addSp .r12 0, .ldrSp .r0 (arg 0), .ldrSp .lr (arg 4), .mov .r2 (.imm 0)]

/-- The `r5` octets drawn wiped, unless there are none (`r2` is still 0). -/
def wipeDrawn : Prog isa :=
  .seq (.block [.cmp .r5 (.imm 0)]) (.ite .eq (.block [])
    (.seq (.block [.addSp .r12 0, .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oBuf)), .mov .lr (.reg .r5)])
      Bignum.Arm.maskBytes))

/-- The tape in `r7`, the budget in `r6`, and Z set if `rand_len` is the budget. -/
def budget : List Instr := [.dp .add .r6 .r3 (.imm 128), .cmp .r8 (.reg .r6)]

/-- Exhausted: `tape` is `[rand_len, 0]`, status 3. -/
def exhausted : List Instr :=
  [.mov .r9 (.imm 0), .str .r8 .r7 0, .str .r9 .r7 4, .str .r9 .r7 8, .str .r9 .r7 12, .mov .r0 (.imm 3)]

/-- More entropy: `tape` is `[0, min(cap, psLen + rand_len - r5)]`, status 0:
with `req = psLen + rand_len - r5` in `r9`, `t = (cap - req) >> 31` (1 exactly
when `req > cap`, all of them below `2 ^ 31`), the minimum is
`cap + ((req - cap) & (t - 1))`. -/
def request : List Instr :=
  [.dp .add .r9 .r3 (.reg .r8), .dp .sub .r9 .r9 (.reg .r5), .dp .sub .r10 .r6 (.reg .r9),
    .mov .r10 (.shifted .r10 .lsr 31), .dp .sub .r10 .r10 (.imm 1), .dp .sub .r11 .r9 (.reg .r6),
    .dp .and .r11 .r11 (.reg .r10), .dp .add .r11 .r11 (.reg .r6), .mov .r10 (.imm 0),
    .str .r10 .r7 0, .str .r10 .r7 4, .str .r11 .r7 8, .str .r10 .r7 12, .mov .r0 (.imm 0)]

def reject : Prog isa :=
  .seq (.block zeroArgs) (.seq Bignum.Arm.maskBytes (.seq wipeDrawn (.seq (.block tapeLoad)
    (.seq (.block budget) (.ite .eq (.block exhausted) (.block request))))))

/-- The inner frame's body. -/
def body (encName : String) (enc : Prog isa) : Prog isa :=
  .seq (.block start) (.seq scan (.seq (.block [.cmp .r5 (.reg .r3)]) (.ite .eq (accept encName enc) reject)))

/-- `vg_rsa_pkcs1_encrypt_random`, calling an implementation of
`vg_rsa_pkcs1_encrypt_precomputed` (`enc`) by its name. -/
def code (encName : String) (enc : Prog isa) : Prog isa := wrap frameBytes (body encName enc)

end VG.Impl.RsaPkcs1Enc.Arm.Random
