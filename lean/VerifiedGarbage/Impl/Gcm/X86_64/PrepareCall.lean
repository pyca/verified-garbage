module

public import VerifiedGarbage.Impl.Gcm.X86_64
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-!
# The 48 prepared powers of a key context, by calls of `vg_ghash` (x86-64)

`vg_aes_gcm_prepare(ctx = rdi)` with an implementation of `vg_ghash`: `prepare`
runs `inner`, written for `(ctx = rdi, scratch = rsi)`, with its 312 bytes
of working space in a frame on the stack, zeroed on return
(`withStackScratchWiped`).

Power `n` of the hash subkey `H` has its slot in the context at `slot n`:
pair `k` is `H²ᵏ⁺²` at `256 + 32k`, then `H²ᵏ⁺¹`. `inner` first stores
`Hⁿ` itself (a big-endian block, as `vg_ghash` reads and writes its
accumulator) in its slot, and later turns it, in place, into
`preparedPower(Hⁿ)` (a little-endian 128-bit word) with the baseline
`vg_ghash`'s own `hInv` (`pp`). Step `n` (`step`) copies `Hⁿ` to the slot
of `Hⁿ⁺¹`, turns `Hⁿ` into its prepared power, moves `rsi` to the next slot
and computes `Hⁿ⁺¹ = Hⁿ • H` there, with a call of the implementation of
`vg_ghash` (`nm`, whose code is `gh`) on one zero block. The next slot is 16
bytes before an odd power's and 48 bytes after an even power's, so the steps
go by pairs (`pair`), all the same code, 23 of them, then step 47 and the
last power's `pp`.

`vg_ghash` writes neither `rsi` nor `r8`: `rsi` holds the current slot and
`r8` the scratch buffer, which holds:

* bytes 0–255: `vg_ghash`'s working space;
* 256–271: a copy of `H`, from bytes 240–255 of the context;
* 272–287: the zero block;
* 288–311: `r12–r14`, which `hInv` writes, saved and restored.

No address and no branch depends on anything but `ctx`, `scratch` and the
stack pointer, which `vg_ghash` keeps public (in `rsi` and `r8`): it is
constant time.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.PrepareCall

open VG.X86_64
open VG.Impl.Gcm.X86_64 (at_ hInv)

/-- The offsets in the scratch buffer. -/
def hO : Nat := 256
def zO : Nat := 272
def savedO : Nat := 288

/-- The bytes of the scratch buffer. -/
def scratchBytes : Nat := 312

/-- The callee-saved registers `hInv` writes, and where they are saved. -/
def saved : List (Reg × Nat) := [(.r12, 0), (.r13, 8), (.r14, 16)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .r8 (savedO + d)) r

def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r8 (savedO + d)))

/-- The block at `rsi` turned into its prepared power, in place: `hInv`
leaves its high half in `r11` and its low half in `r12`. -/
def pp : List Instr :=
  [.mov .rdi (.reg .rsi)] ++ hInv ++ [.store (at_ .rsi 0) .r12, .store (at_ .rsi 8) .r11]

/-- Load `H`, save the registers, copy `H` to the scratch buffer and to the
slot of `H¹` (at `ctx + 272`, which `rsi` then holds), and zero the zero
block. -/
def setup : List Instr :=
  [.mov .rax (.mem (at_ .rdi 240)), .mov .rdx (.mem (at_ .rdi 248)), .mov .r8 (.reg .rsi)] ++ save ++ [
    .store (at_ .r8 hO) .rax, .store (at_ .r8 (hO + 8)) .rdx,
    .store (at_ .rdi 272) .rax, .store (at_ .rdi 280) .rdx,
    .mov .rax (.imm 0), .store (at_ .r8 zO) .rax, .store (at_ .r8 (zO + 8)) .rax,
    .mov .rsi (.reg .rdi), .alu .add .rsi (.imm 272)]

/-- The block at `rsi` copied to `rsi + d`. -/
def copy (d : Int) : List Instr := [
  .mov .rax (.mem { base := .rsi }), .store { base := .rsi, disp := d } .rax,
  .mov .rax (.mem { base := .rsi, disp := 8 }), .store { base := .rsi, disp := d + 8 } .rax]

/-! The implementation of `vg_ghash` the code calls: its name and code. -/

variable (nm : String) (gh : Prog isa)

/-- `vg_ghash(h, rsi, zero, 1, scratch)`, on the accumulator at `rsi`. -/
def mulH : Prog isa :=
  .seq (.block [
    .mov .rdi (.reg .r8), .alu .add .rdi (.imm (BitVec.ofNat 32 hO)),
    .mov .rdx (.reg .r8), .alu .add .rdx (.imm (BitVec.ofNat 32 zO)),
    .mov .rcx (.imm 1)])
    (.call nm gh)

/-- Step `n`, with the slot of `Hⁿ⁺¹` `d` bytes from that of `Hⁿ`. -/
def step (d : Int) : Prog isa :=
  .seq (.block (copy d ++ pp ++ [.alu .add .rsi (.imm (BitVec.ofInt 32 d))])) (mulH nm gh)

/-- From an odd power's slot to the next (16 bytes before it). -/
def stepOdd : Prog isa := step nm gh (-16)

/-- From an even power's slot to the next (48 bytes after it). -/
def stepEven : Prog isa := step nm gh 48

def pair : Prog isa := .seq (stepOdd nm gh) (stepEven nm gh)

/-- `n` pairs. -/
def pairs : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (pairs n) (pair nm gh)

def inner : Prog isa :=
  .seq (.block setup) (.seq (pairs nm gh 23) (.seq (stepOdd nm gh) (.block (pp ++ restore))))

/-- `vg_aes_gcm_prepare`, with its working space on the stack. -/
def prepare : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped (8 + scratchBytes) .rsi (scratchBytes / 8) (inner nm gh)

end VG.Impl.Gcm.X86_64.PrepareCall
