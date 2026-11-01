module

public import VerifiedGarbage.Impl.MlKem.PPC64LE.Top
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Arith

/-!
# ML-DSA on PPC64LE: the pieces of the top-level functions

As on 32-bit ARM (`Impl/MlDsa/Arm/KeyGen/Frag.lean`): the top-level
functions are sequences of calls of ML-DSA's polynomial primitives
(`Proof/MlDsa/Contract.lean`) and of the SHA-3 sponge functions, on buffers in
their working space `scratch` and their arguments. Like ML-KEM's top-level
functions (`Impl/MlKem/PPC64LE/Top.lean`, whose sponge routine `hash`, byte
copy `copy` and saving of our caller's registers they use), they keep
`scratch` in `r31` and their other arguments in `r28`–`r30`, the AND of the
results so far in `r24`, and save our caller's `r24`–`r31` and our return
address in `scratch` (at 840, `oSave`): callee-saved registers, which the
functions they call preserve.

A buffer is at `p.1 + p.2` for a pointer `p` (a register and an offset).
Each call is preceded by the moves of its arguments into `r3`–`r10`
(`glue`): `lis` and `ori` of the offset (or of an integer argument), then an
`add` of the register for a pointer, so that any offset or integer below
2³¹ can be moved, whatever the parameter set. Every argument is in a
register.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.KeyGen

open VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.Arith (loadImm)
open VG.Impl.Sha3.PPC64LE.Stream (mov)

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

/-- The byte `v` to `p` (`v`, `p.2 < 2¹⁵`). -/
def setB (p : Ptr) (v : Nat) : List Instr := [.li .r0 v, .stb .r0 p.1 p.2]

/-- `f a, f (a + 1), …, f (a + n - 1)`, in sequence. -/
def seqR (f : Nat → Prog isa) (a : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (f a) (seqR f (a + 1) n)

/-! ## Results -/

/-- `r3 ←` its low word (the result is a `u32`, and the rest of the register
is anything), then `r24 ← r24 ∧ r3`. -/
def and24 : List Instr := [.lsr .w .r3 .r3 0, .logic .and .r24 .r24 .r3]

def maskBody : List Instr :=
  [.load .w .r6 .r4 0, .logic .and .r6 .r6 .r12, .store .w .r6 .r4 0, .addi .r4 .r4 4, .subi .r5 .r5 1]

/-- The polynomial at `a` masked by the result `r3` (0 or 1, after `and24`)
of the sampler that wrote it: unchanged if 1, and zero if 0, so that it is
reduced either way, without a branch. `r12 ← -r3`, then each coefficient
`∧ r12`. -/
def mask (a : Ptr) : Prog isa :=
  .seq (.block (([.li .r12 0, .sub .r12 .r12 .r3] : List Instr) ++ Arg.instrs .r4 (.ptr a) ++
      ([.li .r5 256] : List Instr)))
    (.loop (.block maskBody) (.nonzero .d .r5))

/-- A sampler's call, its result ANDed into `r24`, and its output masked. -/
def sampled (call : Prog isa) (a : Ptr) : Prog isa :=
  .seq call (.seq (.block and24) (mask a))

/-! ## Entry and exit -/

/-- Our caller's `r24`–`r31` and our return address saved in `scratch` (in
`r6`), the arguments moved to `r28`–`r31`, and `r24 ← 1`. -/
def pro : List Instr :=
  Impl.MlKem.PPC64LE.topSave .r6 ++
    ([mov .r30 .r3, mov .r29 .r4, mov .r28 .r5, mov .r31 .r6, .li .r24 1] : List Instr)

end VG.Impl.MlDsa.PPC64LE.KeyGen
