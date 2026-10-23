module

public import VerifiedGarbage.Impl.Rc2.PPC64LE.Cbc
public import VerifiedGarbage.Impl.Rc2.PPC64LE.ExpandKey

/-! # Streaming RC2-CBC on PPC64LE

`vg_rc2_cbc_init(key = r3, key_len = r4, effective_bits = r5, iv = r6,
iv_len = r7, ctx = r8, scratch = r9)` checks the lengths, returning 1, 2 or
3 for the first that is invalid, copies the IV to `ctx + 128`, calls
`vg_rc2_expand_key(key, key_len, effective_bits, ctx, scratch)` to write the
schedule to `ctx`, and returns 0.

`vg_rc2_cbc_{en,de}crypt_update(ctx = r3, pending_len = r4, data = r5,
len = r6, out = r7, out_len = r8, scratch = r9)`: if `out_len` is 0, it
appends the data to the pending bytes at `ctx + 136 + pending_len`.
Otherwise it copies the pending bytes and the first `out_len - pending_len`
bytes of data to `out`, the rest of the data to `ctx + 136`, and calls the
CBC function on the `out_len / 8` blocks at `out`, with the schedule at
`ctx` and the chaining value at `ctx + 128`.

The working space at `scratch` (`r9`) is the called function's, but for
its last 64 bytes: there the return address, which the call replaces, and
our caller's `r25`, which holds `scratch` across the call, are saved. The
code uses no stack. Bytes are
copied one at a time through advancing pointers, with `r0` holding the
byte. Every branch, loop count and address depends only on the pointers and
lengths.
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

/-- One byte from `src` to `dst + dd`, advancing both pointers, and the
count less one. -/
def copyBody (src dst : Reg) (dd : Nat) (cnt : Reg) : List Instr :=
  [.lbz .r0 src 0, .stb .r0 dst dd, .addi src src 1, .addi dst dst 1, .subi cnt cnt 1]

/-- Copies `cnt` bytes from `src` to `dst + dd`. -/
def copy (src dst : Reg) (dd : Nat) (cnt : Reg) : Prog isa :=
  .ite (.zero .d cnt) (.block []) (.loop (.block (copyBody src dst dd cnt)) (.nonzero .d cnt))

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

/-! ## `update` -/

def cbcCall (d : Spec.Rc2.Direction) : Prog isa :=
  match d with
  | .encrypt => .call "vg_rc2_cbc_encrypt" Cbc.encrypt
  | .decrypt => .call "vg_rc2_cbc_decrypt" Cbc.decrypt

/-- No complete block: the data after the pending bytes. -/
def short : Prog isa := .seq (.block [.add .r10 .r3 .r4]) (copy .r5 .r10 136 .r6)

/-- The pending bytes, from `ctx + 136`, to `out`. -/
def toOut : List Instr := [.addi .r10 .r3 136, mov .r11 .r7, mov .r12 .r4]

/-- The first `out_len - pending_len` bytes of data to `out` after them. -/
def middle : List Instr := [.sub .r12 .r8 .r4]

/-- The rest of the data, `len - (out_len - pending_len)` bytes, to
`ctx + 136`. -/
def toPending : List Instr := [.addi .r10 .r3 136, .sub .r12 .r6 .r8, .add .r12 .r12 .r4]

/-- The arguments of the CBC function: `schedule = ctx`, `iv = ctx + 128`,
`data = out`, `n = out_len / 8`, `scratch`. -/
def cbcArgs : List Instr := [.addi .r4 .r3 128, mov .r5 .r7, .lsr .d .r6 .r8 3, mov .r7 .r9]

def long (d : Spec.Rc2.Direction) : Prog isa :=
  withLr
    (.seq (.block toOut)
      (.seq (copy .r10 .r11 0 .r12)
        (.seq (.block middle)
          (.seq (copy .r5 .r11 0 .r12)
            (.seq (.block toPending)
              (.seq (copy .r5 .r10 0 .r12)
                (.seq (.block cbcArgs) (cbcCall d))))))))

def update (d : Spec.Rc2.Direction) : Prog isa := .ite (.zero .d .r8) short (long d)

def encryptUpdate : Prog isa := update .encrypt
def decryptUpdate : Prog isa := update .decrypt

end VG.Impl.Rc2.PPC64LE.Stream
