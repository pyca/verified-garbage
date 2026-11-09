module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Wrap
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on x86 (32-bit)

`vg_rsa_pkcs1_encrypt_random(out, out_len, tape, n, n_len, e, e_len, msg,
msg_len, rand, rand_len, scratch, scratch_len, pre, pre_len)`, all on the
stack. It draws the padding string `PS` (`psLen = n_len - msg_len - 3`
octets) into its frame and, once it has all of it, calls
`vg_rsa_pkcs1_encrypt_precomputed` (`enc`, by its name `encName`) with it:

1. `head`: `edx` the octets of `PS` still to draw, `esi` the tape, `ecx`
   its octets left, `edi` the end of `PS` so far, in the frame at `oBuf`.
2. `scan` (skipped if `rand_len` is 0): each octet of the tape in turn,
   kept at the end of `PS` unless it is zero, until `PS` is full or the
   tape ends. It branches on whether each octet is zero, which the
   contract makes public, and on the counts, which follow from it.
3. With `PS` full (`accept`): `tape` is `[rand_len - ecx, 0]` (two words
   each), the call's fourteen arguments at the frame's base, the status
   `2 - r` in `ebx` (callee-saved), and `PS` wiped.
4. Otherwise (`reject`): `out` and the octets drawn wiped, and with the
   budget `cap = psLen + 128`: status 3 and `tape = [rand_len, 0]` if
   `rand_len ≥ cap`; else status 0 and `tape = [0, min(cap, rand_len +
   edx)]`, which is more than `rand_len` as `edx > 0`.

The frame (`Impl/RsaPkcs1Sig/X86/Wrap.lean`) holds the call's arguments
from its base and `PS` (up to 1024 bytes) at `oBuf`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.X86.Random

open VG VG.X86
open VG.Impl.RsaPkcs1Sig.X86 (wrap argOff stk at_)

/-- The size of the inner frame. -/
def frameBytes : Nat := 1088

/-- `PS`. -/
def oBuf : Nat := 64

/-- Argument `j` (from 0). -/
def arg (j : Nat) : Src := .mem (stk (argOff frameBytes j))

/-- `psLen = n_len - msg_len - 3` into `r`, with `t` a scratch register. -/
def psLenTo (r t : Reg) : List Instr :=
  [.mov r (arg 4), .mov t (arg 8), .alu .sub r (.reg t), .alu .sub r (.imm 3)]

/-- The scan's registers. -/
def head : List Instr :=
  psLenTo .edx .eax ++ [.mov .esi (arg 9), .mov .ecx (arg 10), .mov .edi (.reg .esp),
    .alu .add .edi (.imm (BitVec.ofNat 32 oBuf)), .alu .cmp .ecx (.imm 0)]

/-- The next octet into `eax`; ZF set if it is zero. -/
def load : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1), .alu .test .eax (.reg .eax)]

/-- A nonzero octet, kept. -/
def keep : List Instr := [.store8 (at_ .edi 0) .al, .alu .add .edi (.imm 1), .alu .sub .edx (.imm 1)]

/-- ZF set if `PS` is full or the tape has ended. -/
def more : Prog isa :=
  .seq (.block [.alu .cmp .edx (.imm 0)]) (.ite .e (.block []) (.block [.alu .test .ecx (.reg .ecx)]))

def step : Prog isa := .seq (.block load) (.seq (.ite .ne (.block keep) (.block [])) more)

def scan : Prog isa := .ite .ne (.loop step .ne) (.block [])

/-- `k` zero bytes from `esi` (`eax` zero, `ecx` the count). -/
def zeroLoop : Prog isa := .loop (.block Impl.Bignum.X86.PublicFn.clearStep) .ne

/-- The tape's pointer. -/
def tapePtr : List Instr := [.mov .eax (arg 2)]

/-- `tape = [rand_len - ecx, 0]`. -/
def tapeAcc : List Instr :=
  [.mov .ebx (arg 10), .alu .sub .ebx (.reg .ecx), .store (at_ .eax 0) .ebx, .mov .ebx (.imm 0),
    .store (at_ .eax 4) .ebx, .store (at_ .eax 8) .ebx, .store (at_ .eax 12) .ebx]

/-- Argument `j` to the call's argument `i`. -/
def copyArg (j i : Nat) : List Instr := [.mov .eax (arg j), .store (stk (4 * i)) .eax]

/-- The call's arguments: `out`, `n_len`, `n`, `n_len`, `e`, `e_len`, `msg`,
`msg_len`, `PS`, `psLen`, `scratch`, `scratch_len`, `pre`, `pre_len`. -/
def callArgs : List Instr :=
  copyArg 0 0 ++ copyArg 4 1 ++ copyArg 3 2 ++ copyArg 4 3 ++ copyArg 5 4 ++ copyArg 6 5 ++ copyArg 7 6 ++
    copyArg 8 7 ++ [.mov .eax (.reg .esp), .alu .add .eax (.imm (BitVec.ofNat 32 oBuf)), .store (stk 32) .eax] ++
    psLenTo .eax .ebx ++ [.store (stk 36) .eax] ++ copyArg 11 10 ++ copyArg 12 11 ++ copyArg 13 12 ++
    copyArg 14 13

/-- The status `2 - eax` into `ebx`, and the wipe's registers: `PS` in
`esi`, `psLen` in `ecx`, `eax` zero. -/
def status : List Instr :=
  [.mov .ebx (.imm 2), .alu .sub .ebx (.reg .eax), .mov .esi (.reg .esp),
    .alu .add .esi (.imm (BitVec.ofNat 32 oBuf))] ++ psLenTo .ecx .eax ++ [.mov .eax (.imm 0)]

def accept (encName : String) (enc : Prog isa) : Prog isa :=
  .seq (.block tapePtr) (.seq (.block tapeAcc) (.seq (.block callArgs) (.seq (.call encName enc)
    (.seq (.block status) (.seq zeroLoop (.block [.mov .eax (.reg .ebx)]))))))

/-- `out` zeroed. -/
def zeroOutArgs : List Instr := [.mov .esi (arg 0), .mov .ecx (arg 4), .mov .eax (.imm 0)]

/-- The `psLen - edx` octets drawn, and ZF set if there are none. -/
def drawnArgs : List Instr :=
  psLenTo .ecx .eax ++ [.alu .sub .ecx (.reg .edx), .mov .esi (.reg .esp),
    .alu .add .esi (.imm (BitVec.ofNat 32 oBuf)), .mov .eax (.imm 0), .alu .test .ecx (.reg .ecx)]

/-- `eax` the tape's length, `ebx` the budget, `esi` the tape; CF clear if
`rand_len ≥ cap`. -/
def budget : List Instr :=
  [.mov .eax (arg 10), .mov .ebx (arg 4), .mov .ecx (arg 8), .alu .sub .ebx (.reg .ecx),
    .alu .add .ebx (.imm 125), .mov .esi (arg 2), .alu .cmp .eax (.reg .ebx)]

/-- Exhausted: `tape = [rand_len, 0]`, status 3. -/
def exhausted : List Instr :=
  [.store (at_ .esi 0) .eax, .mov .eax (.imm 0), .store (at_ .esi 4) .eax, .store (at_ .esi 8) .eax,
    .store (at_ .esi 12) .eax, .mov .eax (.imm 3)]

/-- The request `rand_len + edx` into `eax`; CF set if the budget is less. -/
def reqArgs : List Instr := [.alu .add .eax (.reg .edx), .alu .cmp .ebx (.reg .eax)]

/-- More entropy: `tape = [0, eax]`, status 0. -/
def request : List Instr :=
  [.mov .ebx (.imm 0), .store (at_ .esi 0) .ebx, .store (at_ .esi 4) .ebx, .store (at_ .esi 8) .eax,
    .store (at_ .esi 12) .ebx, .mov .eax (.imm 0)]

def reject : Prog isa :=
  .seq (.block zeroOutArgs) (.seq zeroLoop (.seq (.block drawnArgs) (.seq (.ite .ne zeroLoop (.block []))
    (.seq (.block budget) (.ite .ae (.block exhausted)
      (.seq (.block reqArgs) (.seq (.ite .b (.block [.mov .eax (.reg .ebx)]) (.block [])) (.block request))))))))

/-- The inner frame's body. -/
def body (encName : String) (enc : Prog isa) : Prog isa :=
  .seq (.block head) (.seq scan (.seq (.block [.alu .cmp .edx (.imm 0)]) (.ite .e (accept encName enc) reject)))

/-- `vg_rsa_pkcs1_encrypt_random`, calling an implementation of
`vg_rsa_pkcs1_encrypt_precomputed`'s code `enc` by its name. -/
def code (encName : String) (enc : Prog isa) : Prog isa := wrap frameBytes (body encName enc)

end VG.Impl.RsaPkcs1Enc.X86.Random
