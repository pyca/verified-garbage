module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Returning without secret residue (64-bit RISC-V)

`scrub retBits cs c` runs `c`, then clears everything `c` may have left
where its Rust caller cannot clear it (`RISCV64.NoResidue`), as
`Impl/Scrub/X86_64.lean` does on x86-64:

* the stack below the stack pointer, within its `cs.sum` bytes (the stack
  `c`'s frames use), in nested frames of the sizes `cs` (each at most 2048
  bytes, so that every offset in it is an encodable displacement of `sd`):
  every doubleword of each, from `sp` up, with `sd t0, off(t1)`, where `t0`
  is zero and `t1` the frame's `sp` (`sd` takes no base `sp` in the model), or
  only some of them (`scrubSel`);
* the caller-saved integer registers `a1`–`a7` and `t0`–`t6`, with
  `li r, 0`, and the bits of `a0`, the result, above its `retBits` low ones.

The model has no other register a function may change (see
`TCB/RISCV64/Residue.lean`): `ra` and `s0`–`s11` are restored, and the
floating-point and vector registers and the CSRs are never written.
-/

@[expose] public section

namespace VG.Impl.Scrub.RISCV64

open VG.RISCV64

/-- `li r, 0`. -/
def zeroR (r : Reg) : Instr := .li r 0

/-- The caller-saved integer registers but `a0`. -/
def scratchRegs : List Reg :=
  [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

/-- Clear the bits of `a0` above a result of `retBits` bits: all of them
(`li`), or, for a narrower result, by a shift left then right of the same
amount. -/
def retFix (retBits : Nat) : List Instr :=
  if retBits = 0 then [zeroR .a0]
  else if retBits < 64 then
    [.shift .sll .d .a0 .a0 (64 - retBits), .shift .srl .d .a0 .a0 (64 - retBits)]
  else []

/-- `sd t0, 8k(t1)` for `k` from `k₀` to `k₀ + n - 1`. -/
def stores (k₀ : Nat) : Nat → List Instr
  | 0 => []
  | n + 1 => .store .d .t0 .t1 (8 * k₀) :: stores (k₀ + 1) n

/-- Zero the stack below `sp` in nested frames of the sizes `cs`, each
doubleword of each frame with `t0`, which is zero. -/
def wipe : List Nat → Prog isa
  | [] => .block []
  | b :: bs => .frame (.alloc b) (.seq (.block (.addSp .t1 0 :: stores 0 (b / 8))) (wipe bs)) (.free b)

/-- Frames of at most 2048 bytes (`fuel` of them at most) summing to `n`. -/
def chunksAux : Nat → Nat → List Nat
  | 0, _ => []
  | _ + 1, 0 => []
  | f + 1, n + 1 => if n + 1 ≤ 2048 then [n + 1] else 2048 :: chunksAux f (n + 1 - 2048)

def chunks (n : Nat) : List Nat := chunksAux (n / 2048 + 1) n

/-- The clearing: `t0` zeroed, the stack in frames of the sizes `cs`, then
the result's upper bits and the scratch registers. -/
def scrubTail (retBits : Nat) (cs : List Nat) : Prog isa :=
  .seq (.block [zeroR .t0]) (.seq (wipe cs) (.block (retFix retBits ++ scratchRegs.map zeroR)))

/-- `c`, then the clearing of `stack` bytes of stack. -/
def scrub (retBits stack : Nat) (c : Prog isa) : Prog isa :=
  .seq c (scrubTail retBits (chunks stack))

/-! ## Clearing only some of the stack

`scrubSel retBits fs c` is `scrub`, but its frames, of the sizes `fs.map (·.1)`, zero only
the doublewords of their runs `(k, n)` (`8k` to `8(k + n) - 1` from the frame's base): the
bytes the residue analysis (`RISCV64.RTaint`) finds may differ between two runs. -/

/-- The doublewords of the runs `rs`, from `t1`, zeroed with `t0`. -/
def storesRuns : List (Nat × Nat) → List Instr
  | [] => []
  | (k, n) :: rs => stores k n ++ storesRuns rs

/-- Zero the runs of each frame of `fs`, nested below `sp`. -/
def wipeSel : List (Nat × List (Nat × Nat)) → Prog isa
  | [] => .block []
  | (b, rs) :: bs => .frame (.alloc b) (.seq (.block (.addSp .t1 0 :: storesRuns rs)) (wipeSel bs)) (.free b)

/-- The clearing of `scrubSel`. -/
def scrubTailSel (retBits : Nat) (fs : List (Nat × List (Nat × Nat))) : Prog isa :=
  .seq (.block [zeroR .t0]) (.seq (wipeSel fs) (.block (retFix retBits ++ scratchRegs.map zeroR)))

/-- `c`, then the clearing of the runs of `fs`. -/
def scrubSel (retBits : Nat) (fs : List (Nat × List (Nat × Nat))) (c : Prog isa) : Prog isa :=
  .seq c (scrubTailSel retBits fs)

end VG.Impl.Scrub.RISCV64
