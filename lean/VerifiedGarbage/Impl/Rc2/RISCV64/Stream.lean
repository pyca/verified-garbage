module

public import VerifiedGarbage.Impl.Rc2.RISCV64.Cbc
public import VerifiedGarbage.Impl.Rc2.RISCV64.ExpandKey

/-! # Streaming RC2-CBC on RISC-V

The code of the PPC64LE implementation (`Impl/Rc2/PPC64LE/Stream.lean`).

`vg_rc2_cbc_init(key = a0, key_len = a1, effective_bits = a2, iv = a3,
iv_len = a4, ctx = a5, scratch = a6)` checks the lengths, returning 1, 2 or
3 for the first that is invalid, copies the IV to `ctx + 128`, calls
`vg_rc2_expand_key(key, key_len, effective_bits, ctx, scratch)` to write the
schedule to `ctx`, and returns 0.

`vg_rc2_cbc_{en,de}crypt_update(ctx = a0, pending_len = a1, data = a2,
len = a3, out = a4, out_len = a5, scratch = a6)`: if `out_len` is 0, it
appends the data to the pending bytes at `ctx + 136 + pending_len`.
Otherwise it copies the pending bytes and the first `out_len - pending_len`
bytes of data to `out`, the rest of the data to `ctx + 136`, and calls the
CBC function on the `out_len / 8` blocks at `out`, with the schedule at
`ctx` and the chaining value at `ctx + 128`.

The working space at `scratch` (`a6`) is the called function's, but for
its last 64 bytes: there the return address, which the call replaces, and
our caller's `s7`, which holds `scratch` across the call, are saved. The
code uses no stack. Bytes are copied one at a time through advancing
pointers, with `a7` holding the byte. Every branch, loop count and address
depends only on the pointers and lengths.
-/

@[expose] public section

namespace VG.Impl.Rc2.RISCV64.Stream

open VG.RISCV64
open VG.Impl.Rc2.RISCV64.Cbc (mov)
open VG.Impl.Words.RISCV64 (loadLE64 storeLE64)

/-- `f`, with the return address and `s7` saved at `scratch + 512` and
`scratch + 520`, and `scratch` in `s7`. -/
def withRa (f : Prog isa) : Prog isa :=
  .seq (.block [.store .d .ra .a6 512, .store .d .s7 .a6 520, mov .s7 .a6])
    (.seq f (.block [.load .d .ra .s7 512, .load .d .s7 .s7 520]))

/-- One byte from `src` to `dst + dd`, advancing both pointers, and the
count less one. -/
def copyBody (src dst : Reg) (dd : Nat) (cnt : Reg) : List Instr :=
  [.load .b .a7 src 0, .store .b .a7 dst dd, .addi src src 1, .addi dst dst 1, .addi cnt cnt (-1)]

/-- Copies `cnt` bytes from `src` to `dst + dd`. -/
def copy (src dst : Reg) (dd : Nat) (cnt : Reg) : Prog isa :=
  .ite (.zero cnt) (.block []) (.loop (.block (copyBody src dst dd cnt)) (.nonzero cnt))

/-! ## `init` -/

/-- The IV to `ctx + 128` (through `t2`), and the arguments of
`vg_rc2_expand_key`: `schedule = ctx` in `a3`, `scratch` in `a4`. -/
def initArgs : List Instr :=
  loadLE64 .t0 .a7 .t1 .a3 0 ++ ([.addi .t2 .a5 128] : List Instr) ++ storeLE64 .t0 .a7 .t1 .t2 0 ++
    [mov .a3 .a5, mov .a4 .a6]

def initBody : Prog isa :=
  withRa (.seq (.block initArgs) (.seq (.call "vg_rc2_expand_key" expandKey) (.block [.li .a0 0])))

/-- The checks: `a0` is the error code of the first that fails, and `t0`
is zero if none does. `key_len` is in 1..=128 iff `(key_len - 1) >> 7` is
zero, `effective_bits` in 1..=1024 iff `(effective_bits - 1) >> 10` is, and
`iv_len` is 8 iff `iv_len - 8` is. -/
def checks : Prog isa :=
  .seq (.block [.addi .t0 .a1 (-1), .shift .srl .d .t0 .t0 7])
    (.ite (.nonzero .t0) (.block [.li .a0 1])
      (.seq (.block [.addi .t0 .a2 (-1), .shift .srl .d .t0 .t0 10])
        (.ite (.nonzero .t0) (.block [.li .a0 2])
          (.seq (.block [.addi .t0 .a4 (-8)])
            (.ite (.nonzero .t0) (.block [.li .a0 3]) (.block []))))))

def init : Prog isa := .seq checks (.ite (.nonzero .t0) (.block []) initBody)

/-! ## `update` -/

def cbcCall (d : Spec.Rc2.Direction) : Prog isa :=
  match d with
  | .encrypt => .call "vg_rc2_cbc_encrypt" Cbc.encrypt
  | .decrypt => .call "vg_rc2_cbc_decrypt" Cbc.decrypt

/-- No complete block: the data after the pending bytes. -/
def short : Prog isa := .seq (.block [.add .t0 .a0 .a1]) (copy .a2 .t0 136 .a3)

/-- The pending bytes, from `ctx + 136`, to `out`. -/
def toOut : List Instr := [.addi .t0 .a0 136, mov .t1 .a4, mov .t2 .a1]

/-- The first `out_len - pending_len` bytes of data to `out` after them. -/
def middle : List Instr := [.sub .t2 .a5 .a1]

/-- The rest of the data, `len - (out_len - pending_len)` bytes, to
`ctx + 136`. -/
def toPending : List Instr := [.addi .t0 .a0 136, .sub .t2 .a3 .a5, .add .t2 .t2 .a1]

/-- The arguments of the CBC function: `schedule = ctx`, `iv = ctx + 128`,
`data = out`, `n = out_len / 8`, `scratch`. -/
def cbcArgs : List Instr := [.addi .a1 .a0 128, mov .a2 .a4, .shift .srl .d .a3 .a5 3, mov .a4 .a6]

def long (d : Spec.Rc2.Direction) : Prog isa :=
  withRa
    (.seq (.block toOut)
      (.seq (copy .t0 .t1 0 .t2)
        (.seq (.block middle)
          (.seq (copy .a2 .t1 0 .t2)
            (.seq (.block toPending)
              (.seq (copy .a2 .t0 0 .t2)
                (.seq (.block cbcArgs) (cbcCall d))))))))

def update (d : Spec.Rc2.Direction) : Prog isa := .ite (.zero .a5) short (long d)

def encryptUpdate : Prog isa := update .encrypt
def decryptUpdate : Prog isa := update .decrypt

end VG.Impl.Rc2.RISCV64.Stream
