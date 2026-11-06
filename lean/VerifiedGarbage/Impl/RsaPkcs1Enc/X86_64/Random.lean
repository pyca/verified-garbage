module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on x86-64

`vg_rsa_pkcs1_encrypt_random(out, out_len, tape, n, n_len, e, e_len, msg,
msg_len, rand, rand_len, scratch, scratch_len, pre, pre_len)`: the first six
arguments in registers, the others on the stack. It draws the padding string
`PS` (`psLen = n_len - msg_len - 3` octets) into its frame and, once it has
all of it, calls `vg_rsa_pkcs1_encrypt_precomputed` (`enc`, by its name
`encName`) with it:

1. The arguments it needs again are kept in slots of the frame (`setup`).
2. The scan (`scan`, skipped if `rand_len` is 0): each octet of `rand` in
   turn, in `rax`, kept at the end of `PS` (index `rdx`) unless it is zero,
   until `PS` is full or `rand` ends (index `rcx`). It branches on whether
   each octet is zero, which the contract makes public, and on the two
   indices, which follow from it.
3. With `PS` full (`accept`): `tape` is `[rcx, 0]` (`tapeArgs`), the call's
   arguments are those of `vg_rsa_pkcs1_encrypt_precomputed` with `PS` the
   frame's (`stackArgs`, `regArgs`),
   the status `2 - r` from its result `r` (1 for 1, 2 for 0), and `PS` is
   wiped.
4. Otherwise (`reject`): `out` is zeroed, the `rdx` octets drawn are wiped,
   and with the budget `cap = psLen + 128`: if `rand_len ≥ cap`, status 3 and
   `tape` is `[rand_len, 0]`; else status 0 and `tape` is
   `[0, min(cap, psLen + rand_len - rdx)]`, which is more than `rand_len` as
   `rdx < psLen`.

The frame is `frameBytes` bytes, an odd number of words, so that `rsp` is a
multiple of 16 at the call, as the System V ABI asks: at `rsp`, the call's
eight stack arguments; from `oOut`, the slots; from `oBuf`, `PS`, up to 1024
bytes.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.X86_64.Random

open VG VG.X86_64

/-- The size of the frame. -/
def frameBytes : Nat := 1160

/-- The slots: `out`, `tape`, `n`, `n_len`, `e` and `psLen`. -/
def oOut : Nat := 64
def oTape : Nat := 72
def oN : Nat := 80
def oK : Nat := 88
def oE : Nat := 96
def oPs : Nat := 104
/-- `PS`, up to 1024 bytes. -/
def oBuf : Nat := 128

/-- `[rsp + d]`. -/
def sp (d : Nat) : MemOp := { base := .rsp, disp := (d : Int) }

/-- The stack argument `j` (from 0) of the function, from the frame. -/
def arg (j : Nat) : MemOp := sp (frameBytes + 8 + 8 * j)

/-- `[b + i]`: byte `i` of the buffer at `b`. -/
def bx (b i : Reg) : MemOp := { base := b, index := some i }

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat := 0) : MemOp := { base := b, disp := (d : Int) }

/-- The slots; `psLen`; and the scan's registers: `rand` in `rsi`,
`rand_len` in `r11`, `PS` in `rdi`, the indices `rcx` and `rdx` zero, ZF set
if `rand_len` is 0. -/
def setup : List Instr :=
  [.mov .rax (.reg .r8), .alu .sub .rax (.mem (arg 2)), .alu .sub .rax (.imm 3),
    .mov .rsi (.mem (arg 3)), .mov .r11 (.mem (arg 4)),
    .store (sp oOut) .rdi, .store (sp oTape) .rdx, .store (sp oN) .rcx, .store (sp oK) .r8,
    .store (sp oE) .r9, .store (sp oPs) .rax,
    .mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 oBuf)),
    .mov32 .rcx (.imm 0), .mov32 .rdx (.imm 0), .alu .test .r11 (.reg .r11)]

/-- The octet `rcx` of `rand` into `rax`, and `rcx` past it; ZF set if it is
zero. -/
def load : List Instr :=
  [.movzx8 .rax (bx .rsi .rcx), .alu .add .rcx (.imm 1), .alu .test .rax (.reg .rax)]

/-- A nonzero octet, kept at the end of `PS`. -/
def keep : List Instr := [.store8 (bx .rdi .rdx) .rax, .alu .add .rdx (.imm 1)]

/-- Whether to go on: ZF clear unless `PS` is full or `rand` has ended. -/
def more : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.mem (sp oPs))])
    (.ite .e (.block [.mov32 .rax (.imm 0), .alu .test .rax (.reg .rax)])
      (.block [.mov .rax (.reg .r11), .alu .sub .rax (.reg .rcx)]))

/-- One octet of the scan. -/
def step : Prog isa := .seq (.block load) (.seq (.ite .ne (.block keep) (.block [])) more)

/-- The scan, unless `rand` is empty. -/
def scan : Prog isa := .ite .ne (.loop step .ne) (.block [])

/-- `tape` is `[rcx, 0]`. -/
def tapeArgs : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp oTape))])
    (.block [.store (at_ .rax) .rcx, .mov32 .r10 (.imm 0), .store (at_ .rax 8) .r10])

/-- A stack argument of the call from `src`, at `rsp + d`. -/
def copyArg (src : MemOp) (d : Nat) : List Instr := [.mov .rax (.mem src), .store (sp d) .rax]

/-- The call's stack arguments at `rsp`: `msg`, `msg_len`, `PS`, `psLen`,
`scratch`, `scratch_len`, `pre`, `pre_len`. -/
def stackArgs : Prog isa :=
  .seq (.block (copyArg (arg 1) 0)) (.seq (.block (copyArg (arg 2) 8)) (.seq (.block [.store (sp 16) .rdi])
    (.seq (.block (copyArg (sp oPs) 24)) (.seq (.block (copyArg (arg 5) 32))
      (.seq (.block (copyArg (arg 6) 40)) (.seq (.block (copyArg (arg 7) 48))
        (.block (copyArg (arg 8) 56))))))))

/-- The call's register arguments: `out`, `n_len`, `n`, `n_len`, `e`,
`e_len`. -/
def regArgs : List Instr :=
  [.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oK)), .mov .rdx (.mem (sp oN)),
    .mov .rcx (.mem (sp oK)), .mov .r8 (.mem (sp oE)), .mov .r9 (.mem (arg 0))]

/-- The status `2 - eax` into `r11`, and the wipe's registers: `PS` in
`rdi`, `psLen` in `rcx`, the index `r10` and `rax` zero. -/
def status : List Instr :=
  [.mov32 .r11 (.imm 2), .alu32 .sub .r11 (.reg .rax), .mov .rdi (.reg .rsp),
    .alu .add .rdi (.imm (BitVec.ofNat 32 oBuf)), .mov .rcx (.mem (sp oPs)), .mov32 .r10 (.imm 0),
    .mov32 .rax (.imm 0)]

/-- `rdi[r10] := 0` for `r10` up to `rcx`, at least one byte. -/
def wipe : Prog isa :=
  .loop (.block [.store8 (bx .rdi .r10) .rax, .alu .add .r10 (.imm 1), .alu .cmp .r10 (.reg .rcx)]) .ne

/-- `PS` full: the call, and the status. -/
def accept (encName : String) (enc : Prog isa) : Prog isa :=
  .seq (.seq tapeArgs (.seq stackArgs (.block regArgs))) (.seq (.call encName enc)
    (.seq (.block status) (.seq wipe (.block [.mov32 .rax (.reg .r11)]))))

/-- `out` zeroed, `n_len` bytes, at least one; `rdx`, `rcx` and `r11` kept. -/
def zeroOut : Prog isa :=
  .seq (.block [.mov .rdi (.mem (sp oOut)), .mov .r10 (.mem (sp oK)), .mov32 .rax (.imm 0)])
    (.loop (.block [.store8 (at_ .rdi) .rax, .alu .add .rdi (.imm 1), .alu .sub .r10 (.imm 1)]) .ne)

/-- The `rdx` octets drawn wiped, unless there are none. -/
def wipeDrawn : Prog isa :=
  .seq (.block [.mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 oBuf)),
      .mov32 .r10 (.imm 0), .mov .rcx (.reg .rdx), .alu .test .rdx (.reg .rdx)])
    (.ite .ne wipe (.block []))

/-- The budget into `r10`, `tape` into `r8`, CF clear if `rand_len` is at
least the budget. -/
def budget : List Instr :=
  [.mov .r10 (.mem (sp oPs)), .alu .add .r10 (.imm 128), .mov .r8 (.mem (sp oTape)),
    .alu .cmp .r11 (.reg .r10)]

/-- Exhausted: `tape` is `[rand_len, 0]`, status 3. -/
def exhausted : List Instr :=
  [.store (at_ .r8) .r11, .mov32 .rax (.imm 0), .store (at_ .r8 8) .rax, .mov32 .rax (.imm 3)]

/-- More entropy: `tape` is `[0, min(cap, psLen + rand_len - rdx)]`,
status 0. -/
def request : List Instr :=
  [.mov32 .rax (.imm 0), .store (at_ .r8) .rax, .mov .r9 (.mem (sp oPs)), .alu .add .r9 (.reg .r11),
    .alu .sub .r9 (.reg .rdx), .alu .cmp .r10 (.reg .r9), .cmov .b .r9 (.reg .r10),
    .store (at_ .r8 8) .r9]

/-- `PS` not full. -/
def reject : Prog isa :=
  .seq zeroOut (.seq wipeDrawn (.seq (.block budget) (.ite .ae (.block exhausted) (.block request))))

/-- The body of the frame. -/
def body (encName : String) (enc : Prog isa) : Prog isa :=
  .seq (.block setup) (.seq scan (.seq (.block [.alu .cmp .rdx (.mem (sp oPs))])
    (.ite .e (accept encName enc) reject)))

/-- `vg_rsa_pkcs1_encrypt_random`, calling an implementation of
`vg_rsa_pkcs1_encrypt_precomputed`'s code `enc` by its name. -/
def code (encName : String) (enc : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body encName enc) (.free frameBytes)

end VG.Impl.RsaPkcs1Enc.X86_64.Random
