module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.RISCV64.Precomputed

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on RISC-V

`vg_rsa_pkcs1_encrypt_random(out = a0, out_len = a1, tape = a2, n = a3,
n_len = a4, e = a5, e_len = a6, msg = a7, msg_len, rand, rand_len, scratch,
scratch_len, pre, pre_len)`, the last seven on the stack. In the frame of
`vg_rsa_pkcs1_verify_precomputed` (`Impl/RsaPkcs1Sig/RISCV64/Frame.lean`),
whose saves keep `s1`–`s4` and the return address:

1. `psLen = n_len - msg_len - 3` into `s1`, and the scan's registers: `rand`
   in `t3`, `rand_len` in `t4`, `PS` (at `oEM1`) in `t1`, the indices `t2`
   (octets read) and `t5` (octets kept) zero (`setup`).
2. The scan (`scan`, skipped if `rand_len` is 0): octet `t2` of `rand` into
   `t6`, kept at the end of `PS` unless it is zero, until `PS` is full or
   `rand` ends. It branches on whether each octet is zero, which the
   contract makes public, and on the two indices, which follow from it.
3. With `PS` full (`accept`): `tape` is `[t2, 0]`; the arguments of
   `vg_rsa_pkcs1_encrypt_precomputed` (`enc`), its stack arguments in a frame
   of 48 bytes below ours; the status `2 - a0`; `PS` wiped.
4. Otherwise (`reject`): `out` zeroed, the `t5` octets drawn wiped, and with
   the budget `cap = psLen + 128` in `t0`: if `rand_len < cap`, status 0 and
   `tape` is `[0, min(cap, psLen + rand_len - t5)]`; else status 3 and `tape`
   is `[rand_len, 0]`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.RISCV64.Random

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64

/-- `PS`'s place in the frame. -/
def oPS : Nat := oEM1

/-- The saves, `psLen` into `s1`, and the scan's registers. -/
def setup : List Instr :=
  save ++ argBase ++
  [.load .d .t2 .t6 0, .load .d .t3 .t6 8, .load .d .t4 .t6 16, .sub .t5 .a4 .t2, .addi .s1 .t5 (-3),
    .addi .t1 .t0 oPS, .li .t2 0, .li .t5 0]

/-- One octet of the scan: octet `t2` of `rand` into `t6`, kept at the end of
`PS` if it is not zero; `t0` is then zero unless the scan goes on. -/
def step : Prog isa :=
  .seq (.block [.add .t6 .t3 .t2, .load .b .t6 .t6 0, .addi .t2 .t2 1])
    (.seq (.ite (.nonzero .t6) (.block [.add .t0 .t1 .t5, .store .b .t6 .t0 0, .addi .t5 .t5 1]) (.block []))
      (.ite (.eq .t5 .s1) (.block [.li .t0 0]) (.block [.sub .t0 .t4 .t2])))

/-- The scan, unless `rand` is empty. -/
def scan : Prog isa := .ite (.nonzero .t4) (.loop step (.nonzero .t0)) (.block [])

/-- `tape` is `[t2, 0]`; the call's register arguments, and its stack
arguments other than `PS` and `psLen` into `t2`–`t5`. -/
def callRegs : List Instr :=
  [.store .d .t2 .a2 0, .li .t0 0, .store .d .t0 .a2 8, mov .a1 .a4, mov .a2 .a3, mov .a3 .a4, mov .a4 .a5,
    mov .a5 .a6, mov .a6 .a7] ++ argBase ++
  [.load .d .a7 .t6 0, .load .d .t2 .t6 24, .load .d .t3 .t6 32, .load .d .t4 .t6 40, .load .d .t5 .t6 48]

/-- The call's stack arguments, at the stack pointer of its frame. -/
def callStack : List Instr :=
  [.addSp .t0 0, .store .d .t1 .t0 0, .store .d .s1 .t0 8, .store .d .t2 .t0 16, .store .d .t3 .t0 24,
    .store .d .t4 .t0 32, .store .d .t5 .t0 40]

/-- `vg_rsa_pkcs1_encrypt_precomputed`'s symbol. -/
def encName : String := "vg_rsa_pkcs1_encrypt_precomputed"

/-- The call, in a frame of 48 bytes holding its stack arguments. -/
def call : Prog isa :=
  .frame (.alloc 48) (.seq (.block callStack) (.call encName Impl.RsaPkcs1Enc.RISCV64.Precomputed.code))
    (.free 48)

/-- The status `2 - a0`, and `fillLoop`'s registers to wipe `PS`. -/
def status : List Instr :=
  [.li .t0 2, .sub .a0 .t0 .a0, .addSp .t0 0, .addi .a1 .t0 oPS, mov .t5 .s1, .li .t0 0]

/-- `PS` full. -/
def accept : Prog isa :=
  .seq (.block callRegs) (.seq call (.seq (.block status) (.seq fillLoop (.block restore))))

/-- `out` zeroed, `n_len` bytes; the count `t5` kept in `t3`. -/
def zeroOut : Prog isa :=
  .seq (.block [mov .t3 .t5, mov .a1 .a0, mov .t5 .a4, .li .t0 0]) fillLoop

/-- The `t3` octets drawn wiped, unless there are none. -/
def wipeDrawn : Prog isa :=
  .ite (.nonzero .t3) (.seq (.block [.addSp .t0 0, .addi .a1 .t0 oPS, mov .t5 .t3, .li .t0 0]) fillLoop)
    (.block [])

/-- More entropy: `tape` is `[0, min(cap, psLen + rand_len - t3)]`, status 0. -/
def request : Prog isa :=
  .seq (.block [.li .t1 0, .store .d .t1 .a2 0, .add .t1 .s1 .t4, .sub .t1 .t1 .t3])
    (.seq (.ite (.ltu .t0 .t1) (.block [mov .t1 .t0]) (.block []))
      (.block [.store .d .t1 .a2 8, .li .a0 0]))

/-- Exhausted: `tape` is `[rand_len, 0]`, status 3. -/
def exhausted : List Instr := [.store .d .t4 .a2 0, .li .t1 0, .store .d .t1 .a2 8, .li .a0 3]

/-- `PS` not full. -/
def reject : Prog isa :=
  .seq zeroOut (.seq wipeDrawn (.seq (.block [.addi .t0 .s1 128])
    (.seq (.ite (.ltu .t4 .t0) request (.block exhausted)) (.block restore))))

/-- The body of the frame. -/
def body : Prog isa := .seq (.block setup) (.seq scan (.ite (.eq .t5 .s1) accept reject))

/-- `vg_rsa_pkcs1_encrypt_random`. -/
def code : Prog isa := .frame (.alloc frameBytes) body (.free frameBytes)

end VG.Impl.RsaPkcs1Enc.RISCV64.Random
