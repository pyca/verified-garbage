module

public import VerifiedGarbage.Impl.Rc2.PPC64LE.Cbc
public import VerifiedGarbage.Impl.Rc2.PPC64LE.ExpandKey

/-! # Streaming RC2-CBC on PPC64LE

`vg_rc2_cbc_init(key = r3, key_len = r4, effective_bits = r5, iv = r6,
iv_len = r7, ctx = r8, scratch = r9)` checks the lengths, returning 1, 2 or
3 for the first that is invalid, copies the IV to `ctx + 128`, calls
`vg_rc2_expand_key(key, key_len, effective_bits, ctx, scratch)` to write the
schedule to `ctx`, and returns 0.

The working space at `scratch` (`r9`) is the called function's, but for
its last 64 bytes: there the return address, which the call replaces, and
our caller's `r25`, which holds `scratch` across the call, are saved. The
code uses no stack. Every branch and address depends only on the pointers
and lengths.
-/

@[expose] public section

namespace VG.Impl.Rc2.PPC64LE.Stream

open VG.PPC64LE
open VG.Impl.Rc2.PPC64LE.Cbc (mov)

/-- `f`, with the link register and `r25` saved at `scratch + 512` and
`scratch + 520`, and `scratch` in `r25`. -/
def withLr (f : Prog isa) : Prog isa :=
  .seq (.block [.mflr .r0, .store .d .r0 .r9 512, .store .d .r25 .r9 520, mov .r25 .r9])
    (.seq f (.block [.load .d .r0 .r25 512, .mtlr .r0, .load .d .r25 .r25 520]))

/-! ## `init` -/

/-- The IV to `ctx + 128`, and the arguments of `vg_rc2_expand_key`:
`schedule = ctx` in `r6`, `scratch` in `r7`. -/
def initArgs : List Instr := [.load .d .r10 .r6 0, .store .d .r10 .r8 128, mov .r6 .r8, mov .r7 .r9]

def initBody : Prog isa :=
  withLr (.seq (.block initArgs) (.seq (.call "vg_rc2_expand_key" expandKey) (.block [.li .r3 0])))

/-- The checks: `r3` is the error code of the first that fails, and `r10`
is zero if none does. `key_len` is in 1..=128 iff `(key_len - 1) >> 7` is
zero, `effective_bits` in 1..=1024 iff `(effective_bits - 1) >> 10` is, and
`iv_len` is 8 iff `iv_len - 8` is. -/
def checks : Prog isa :=
  .seq (.block [.subi .r10 .r4 1, .lsr .d .r10 .r10 7])
    (.ite (.nonzero .d .r10) (.block [.li .r3 1])
      (.seq (.block [.subi .r10 .r5 1, .lsr .d .r10 .r10 10])
        (.ite (.nonzero .d .r10) (.block [.li .r3 2])
          (.seq (.block [.subi .r10 .r7 8])
            (.ite (.nonzero .d .r10) (.block [.li .r3 3]) (.block []))))))

def init : Prog isa := .seq checks (.ite (.nonzero .d .r10) (.block []) initBody)

end VG.Impl.Rc2.PPC64LE.Stream
