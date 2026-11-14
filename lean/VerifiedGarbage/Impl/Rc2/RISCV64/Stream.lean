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

The working space at `scratch` (`a6`) is the called function's, but for
its last 64 bytes: there the return address, which the call replaces, and
our caller's `s7`, which holds `scratch` across the call, are saved. The
code uses no stack. Every branch and address depends only on the pointers
and lengths.
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

end VG.Impl.Rc2.RISCV64.Stream
