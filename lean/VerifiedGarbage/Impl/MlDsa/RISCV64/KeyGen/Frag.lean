module

public import VerifiedGarbage.Impl.MlKem.RISCV64.Top
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Arith

/-!
# ML-DSA on RISC-V: the pieces of the top-level functions

As on PPC64LE (`Impl/MlDsa/PPC64LE/KeyGen/Frag.lean`): the top-level
functions are sequences of calls of ML-DSA's polynomial primitives
(`Proof/MlDsa/Contract.lean`) and of the SHA-3 sponge functions, on buffers in
their working space `scratch` and their arguments. Like ML-KEM's top-level
functions (`Impl/MlKem/RISCV64/Top.lean`, whose sponge routine `hash`, byte
copy `copy` and saving of our caller's registers they use), they keep
`scratch` in `s11` and their other arguments in `s8`–`s10`, the AND of the
results so far in `s4`, and save our caller's `s3`–`s11` and our return
address in `scratch` (at 1288, `oSave`): callee-saved registers, which the
functions they call preserve.

A buffer is at `p.1 + p.2` for a pointer `p` (a register and an offset).
Each call is preceded by the moves of its arguments into `a0`–`a7`
(`glue`): `lui` and `addi` of the offset (or of an integer argument,
`Arith.loadImm`), then an `add` of the register for a pointer, so that any
offset or integer below `2³¹ - 2048` can be moved, whatever the parameter
set. Every argument is in a register.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.KeyGen

open VG.RISCV64
open VG.Impl.MlDsa.RISCV64.Arith (loadImm)
open VG.Impl.Sha3.RISCV64.Stream (mov)

/-- A pointer: a register and an offset. -/
abbrev Ptr := Reg × Nat

/-! ## Moves -/

/-- An argument: a pointer, or an integer. -/
inductive Arg
  | ptr (p : Ptr)
  | imm (v : Nat)

/-- `d ← a`. -/
def Arg.instrs (d : Reg) : Arg → List Instr
  | .ptr p => loadImm d p.2 ++ ([.add d p.1 d] : List Instr)
  | .imm v => loadImm d v

/-- The moves of the arguments `as` into their registers. -/
def glue : List (Reg × Arg) → List Instr
  | [] => []
  | (d, a) :: as => a.instrs d ++ glue as

/-- The moves of the arguments, then a call. -/
def callAt (name : String) (c : Prog isa) (as : List (Reg × Arg)) : Prog isa :=
  .seq (.block (glue as)) (.call name c)

/-- The byte `v` to `p` (`v`, `p.2 < 2¹¹`), through `t0`. -/
def setB (p : Ptr) (v : Nat) : List Instr := [.li .t0 v, .store .b .t0 p.1 p.2]

/-- `f a, f (a + 1), …, f (a + n - 1)`, in sequence. -/
def seqR (f : Nat → Prog isa) (a : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (f a) (seqR f (a + 1) n)

/-! ## Results -/

/-- `a0 ←` its low word, zero-extended (the result is a `u32`, and the rest
of the register is anything), then `s4 ← s4 ∧ a0`. -/
def and24 : List Instr := [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32, .logic .and .s4 .s4 .a0]

def maskBody : List Instr :=
  [.load .w .a3 .a1 0, .logic .and .a3 .a3 .t1, .store .w .a3 .a1 0, .addi .a1 .a1 4, .addi .a2 .a2 (-1)]

/-- The polynomial at `a` masked by the result `a0` (0 or 1, after `and24`)
of the sampler that wrote it: unchanged if 1, and zero if 0, so that it is
reduced either way, without a branch. `t1 ← -a0`, then each coefficient
`∧ t1`. -/
def mask (a : Ptr) : Prog isa :=
  .seq (.block (([.li .t1 0, .sub .t1 .t1 .a0] : List Instr) ++ Arg.instrs .a1 (.ptr a) ++
      ([.li .a2 256] : List Instr)))
    (.loop (.block maskBody) (.nonzero .a2))

/-- A sampler's call, its result ANDed into `s4`, and its output masked. -/
def sampled (call : Prog isa) (a : Ptr) : Prog isa :=
  .seq call (.seq (.block and24) (mask a))

/-! ## Entry and exit -/

/-- Our caller's `s3`–`s11` and our return address saved in `scratch` (in
`a3`), the arguments moved to `s8`–`s11`, and `s4 ← 1`. -/
def pro : List Instr :=
  Impl.MlKem.RISCV64.topSave .a3 ++
    ([mov .s10 .a0, mov .s9 .a1, mov .s8 .a2, mov .s11 .a3, .li .s4 1] : List Instr)

end VG.Impl.MlDsa.RISCV64.KeyGen
