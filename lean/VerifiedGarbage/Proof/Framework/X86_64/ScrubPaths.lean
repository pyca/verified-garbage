module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChecks

/-!
# The checks of the scrub along a path, compiled (x86-64)

Whether the vectors' upper halves agree after code in two runs of the same
path (`UpperLock.up`), and whether its MXCSR does (`Mx.mx`): the checks of
the scrub that only its own modules use (`UpperLock.lean`, `ScrubOr.lean`),
compiled as those of `ScrubChecks.lean` are, and apart from them so that a
change to one rebuilds only those modules and what imports them.
-/

@[expose] public section

namespace VG.X86_64

namespace UpperLock

/-- Whether the upper halves agree after `i`, given whether they agreed before it. -/
def stepI (a : Bool) (i : Instr) : Bool :=
  match i with
  | .vop .vzeroupper => true
  | i => a && i.vecLevel == 0

/-- Whether the upper halves agree after `c`, given whether they agreed before
it. A loop's body is followed once, from the start of the loop: they then
agree after it from a start at which they agree too (`up_mono`), as at each
later iteration. -/
def up : Prog isa → Bool → Bool
  | .block is, a => is.foldl stepI a
  | .seq x y, a => up y (up x a)
  | .ite _ t e, a => up t a && up e a
  | .loop b _, a => up b a
  | .call _ b, a => up b a
  | .frame _ b _, a => up b a
  | .icall _ _ b n, a => up b a && up n a

/-- The functions `c` may call indirectly. -/
def inames : Prog isa → List String
  | .block _ => []
  | .seq x y => inames x ++ inames y
  | .ite _ t e => inames t ++ inames e
  | .loop b _ => inames b
  | .call _ b => inames b
  | .frame _ b _ => inames b
  | .icall _ n b nx => n :: inames b ++ inames nx

end UpperLock

namespace RScrub.Mx

open VG.X86_64.RTaint (storeW writesMem)

/-- A fact two runs agree on: the low 32 bits of a register, or the 4 bytes
at `d` from a register. -/
inductive F where
  | reg (r : Reg)
  | slot (b : Reg) (d : Int)
  deriving DecidableEq

/-- An operand without an index, with a displacement of 32 bits. -/
def plain (m : MemOp) : Bool := m.index.isNone && decide (-2 ^ (31 : Nat) ≤ m.disp ∧ m.disp < 2 ^ (31 : Nat))

def slotOf (m : MemOp) : F := .slot m.base m.disp

/-- Whether a fact survives `i`: it writes neither the register nor (or its
base register) the bytes. -/
def keep (i : Instr) : F → Bool
  | .reg r => !Taint.clobbers i r
  | .slot b d => !Taint.clobbers i b && match storeW i with
    | some (m, w) => plain m && m.base == b && decide (w ≤ 64) &&
        decide (-2 ^ (31 : Nat) ≤ d ∧ d < 2 ^ (31 : Nat)) &&
        decide (m.disp + w ≤ d ∨ d + 4 ≤ m.disp)
    | none => !writesMem i

/-- The facts `i` establishes, given `fs` before it. -/
def adds (fs : List F) : Instr → List F
  | .stmxcsr m => if plain m then [slotOf m] else []
  | .mov32 r (.imm _) => [.reg r]
  | .mov32 r (.mem m) => if plain m && fs.contains (slotOf m) then [.reg r] else []
  | .alu32 .and r (.imm _) => if fs.contains (.reg r) then [.reg r] else []
  | .alu32 .or r (.imm _) => if fs.contains (.reg r) then [.reg r] else []
  | .store32 m r => if plain m && fs.contains (.reg r) then [slotOf m] else []
  | _ => []

/-- `ldmxcsr` loads bytes agreed on. -/
def ldOk (fs : List F) : Instr → Bool
  | .ldmxcsr m => plain m && fs.contains (slotOf m)
  | _ => true

def step (fs : List F) (i : Instr) : Option (List F) :=
  if ldOk fs i then some (adds fs i ++ fs.filter (keep i)) else none

def blk : List F → List Instr → Option (List F)
  | fs, [] => some fs
  | fs, i :: is => (step fs i).bind (blk · is)

/-- The facts on registers other than `rsp`, which calls and frames keep. -/
def regs (fs : List F) : List F := fs.filter fun f => match f with
  | .reg r => r != .rsp
  | .slot .. => false

/-- Whether nothing in `c` drops the fact `f`: every instruction keeps it,
and `c` calls nothing and has no frame unless `f` is one `regs` keeps. -/
def kept (f : F) : Prog isa → Bool
  | .block is => is.all (keep · f)
  | .seq x y => kept f x && kept f y
  | .ite _ t e => kept f t && kept f e
  | .loop b _ => kept f b
  | .call _ b => !(regs [f]).isEmpty && kept f b
  | .frame _ b j => !(regs [f]).isEmpty && kept f b && keep j f
  | .icall .. => false

/-- The facts after `c`, given `fs` before it, if every `ldmxcsr` in it
loads bytes agreed on. A loop's are those after its body from those of `fs`
that nothing in its body drops (`kept`), which runs the body once however
deep its loops are nested: not those an iteration drops and establishes
again, which are among the facts after the body all the same unless they
were established from themselves. -/
def mx : Prog isa → List F → Option (List F)
  | .block is, fs => blk fs is
  | .seq x y, fs => (mx x fs).bind (mx y)
  | .ite _ t e, fs =>
    match mx t fs, mx e fs with
    | some a, some b => some (a.filter b.contains)
    | _, _ => none
  | .loop b _, fs =>
    match mx b (fs.filter (kept · b)) with
    | some g => if (fs.filter (kept · b)).all g.contains then some g else none
    | none => none
  | .call _ b, fs => (mx b (regs fs)).map regs
  | .frame _ b j, fs => (mx b (regs fs)).map fun g => regs (g.filter (keep j))
  | .icall .., _ => none

end RScrub.Mx

end VG.X86_64
