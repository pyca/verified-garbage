module

public import VerifiedGarbage.Impl.Scrub.X86_64
public import VerifiedGarbage.TCB.Sig

/-!
# What the emitter computes of x86-64 code to scrub it

The registrations of x86-64 functions that return without secret residue
(`Scrub.withScrubAll`, `RScrub.withScrub` and the others) decide how to
scrub a function when the emitter evaluates them: the level its vector
registers are cleared at, the registers it may have written, the stack it
uses, what it leaves in MXCSR. Each is a pass over the function's code, and
over the code of every function it calls, at each call.

This module holds those functions, and nothing else: it imports only the
trusted base and `Impl/Scrub/X86_64.lean`, the code they scrub with, which
imports only the trusted base, so that both are compiled (`NativeTactics` in
the lakefile). The interpreter, which runs the registrations, took most of
the emitter's time on x86-64 to run them: it ran a closure for every
instruction of every pass. The proofs about each function are where they
were, in the module its docs name.

A pass a registration needs goes here, with a name, not as a `fun` in the
registration function (`allLevel` below): the interpreter would run that
`fun` for every instruction, wherever the function it is given to is
compiled.
-/

@[expose] public section

namespace VG.X86_64

open VG.Impl.Scrub.X86_64 (VecLevel)

/-! ## Instructions -/

/-- Whether an instruction loads MXCSR. -/
def loadsMxcsr : Instr → Bool
  | .ldmxcsr _ => true
  | _ => false

/-- The vector state and MXCSR an instruction may write: 0 for none of bits
511:128 of `zmm0`–`zmm15`, nor `zmm16`–`zmm31`, nor MXCSR; 1 for bits 511:128
of `zmm0`–`zmm15` too; 2 for the rest (see `ResidueKeep.lean`). -/
def Instr.vecLevel : Instr → Nat
  | .vop _ | .vmovdquLoad .. | .vmovdquTbl .. | .vbroadcasti128 .. | .vbinLoad ..
  | .vpmadd52Load .. | .zop _ | .vmovdqu32Load .. | .vbroadcasti32x4 .. | .zbcst ..
  | .vpbroadcastdZ .. | .zbcstd .. | .kLoad .. | .kLoad8 .. => 1
  | .vbroadcasti32x4H .. | .eop _ | .evLoad .. | .evMadd52Load .. | .ldmxcsr _
  | .e5op _ | .evBroadcastLoad .. | .e5InsertLoad .. => 2
  | _ => 0

/-- The level of the vector registers alone: `vecLevel`, but `ldmxcsr`, which
writes only MXCSR, at level 0 (see `ResidueKeep.lean`). -/
def Instr.vecLevelR (i : Instr) : Nat := if loadsMxcsr i then 0 else i.vecLevel

namespace Taint

/-- The general-purpose register an instruction writes, if it writes exactly
one (none for stores and SSE instructions, and for `mul` and `mulx`, which
write two). -/
def dstOf : Instr → Option Reg
  | .mov d _ | .mov32 d _ | .alu _ d _ | .alu32 _ d _ | .shift32 _ d _ | .bswap32 d
  | .rorx32 d .. | .andn32 d .. | .rorx d .. | .andn d .. | .movzx8 d _ | .movzx16 d _ | .bswap d | .shift _ d _
  | .shiftCl _ d | .shiftx _ d .. | .movImm64 d _ | .leaSym d _ | .adcx d _ | .adox d _ | .cmov _ d _
  | .vpmovmskb _ d _ | .vpcmpltuw d .. | .movqR d _ | .imul d _ | .imul3 d .. | .shld d .. | .btr d _ | .aluTbl _ d .. => some d
  | .store .. | .store32 .. | .store8 .. | .store16 .. | .movdquLoad .. | .movdquStore .. | .movdquTbl .. | .xop _
  | .vop _
  | .vmovdquLoad .. | .vmovdquStore .. | .vmovdquTbl .. | .vbroadcasti128 .. | .vbinLoad .. | .zop _
  | .vmovdqu32Load .. | .vmovdqu32Store .. | .vbroadcasti32x4 .. | .vbroadcasti32x4H .. | .zbcst .. | .vpbroadcastdZ .. | .zbcstd .. | .vpmadd52Load ..
  | .stmxcsr _ | .ldmxcsr _
  | .eop _ | .evLoad .. | .evStore .. | .evMadd52Load .. | .kLoad .. | .kStore .. | .kLoad8 .. | .kStore8 .. | .lfence
  | .e5op _ | .evBroadcastLoad .. | .e5InsertLoad .. | .e5ExtractStore ..
  | .mul _ | .mulx .. | .push _ | .pop .. | .alloc _ | .free _ | .callr _ => none

/-- Whether an instruction may write the general-purpose register `r`. -/
def clobbers (i : Instr) (r : Reg) : Bool :=
  match i with
  | .mul _ => r == .rax || r == .rdx
  | .mulx hi lo _ => r == hi || r == lo
  -- The push and pop of a frame move `rsp`, and the pop loads `d`.
  | .push _ | .alloc _ | .free _ => r == .rsp
  | .pop d _ => r == .rsp || r == d
  | _ => dstOf i == some r

end Taint

/-! ## MXCSR as a function of MXCSR on entry (`Mxcsr.lean`) -/

/-- `stmxcsr [m]; mov r32, [m]; and r32, 0xFFFF`: MXCSR, but for its
reserved bits, in `r`. -/
def mxcsrSave (m : MemOp) (r : Reg := .r11) : List Instr :=
  [.stmxcsr m, .mov32 r (.mem m), .alu32 .and r (.imm 0xFFFF)]

/-- `mov [m], r32; ldmxcsr [m]`: MXCSR from `r`. -/
def mxcsrRestore (m : MemOp) (r : Reg := .r11) : List Instr := [.store32 m r, .ldmxcsr m]

/-- The operand and register of a block that may be `mxcsrSave`. -/
def saveOp : List Instr → Option (MemOp × Reg)
  | .stmxcsr m :: .mov32 r _ :: _ => some (m, r)
  | _ => none

/-- The operand of a block that may be `mxcsrRestore`. -/
def restoreOp : List Instr → Option MemOp
  | .store32 m _ :: _ => some m
  | _ => none

/-- What code leaves in MXCSR: what it held on entry (`keep`), or that but
for its reserved bits (`mask`, what `mxcsrSave` then `mxcsrRestore` leave). -/
inductive MxC where
  | keep
  | mask
  deriving DecidableEq

/-- MXCSR after code of class `k`, from `x` on entry. -/
def MxC.app : MxC → BitVec 32 → BitVec 32
  | .keep, x => x
  | .mask, x => x &&& 0xFFFF

/-- The class of code of class `a`, then of class `b`. -/
def MxC.comp : MxC → MxC → MxC
  | .keep, .keep => .keep
  | _, _ => .mask

/-- `restores`, computed (with `Code.all`), for the emitter. -/
def restoresC (a b : Prog isa) : Bool :=
  match a, b with
  | .block is, .seq mid (.block js) =>
    match saveOp is, restoreOp js with
    | some (m, r), some m' =>
      is == mxcsrSave m r && js == mxcsrRestore m' r && mid.all fun i => !Taint.clobbers i r
    | _, _ => false
  | _, _ => false

/-- The class of what `c` leaves in MXCSR, if every path through it leaves
the same function of MXCSR on entry (see `Mxcsr.lean`). -/
def mxClass : Prog isa → Option MxC
  | .block is => if is.all (fun i => !loadsMxcsr i) then some .keep else none
  | .seq a b =>
    if restoresC a b then some .mask else
    match mxClass a, mxClass b with
    | some x, some y => some (x.comp y)
    | _, _ => none
  | .ite _ t e =>
    match mxClass t, mxClass e with
    | some x, some y => if x = y then some x else none
    | _, _ => none
  | .loop b _ => mxClass b
  | .call _ b => mxClass b
  | .frame i b j => if !loadsMxcsr i && !loadsMxcsr j then mxClass b else none
  | .icall i _ b n =>
    if loadsMxcsr i then none else
    match mxClass b, mxClass n with
    | some x, some y => if x = y then some x else none
    | _, _ => none

namespace RTaint

/-- The memory an instruction may write: its operand and width. -/
def storeW : Instr → Option (MemOp × Nat)
  | .store m _ => some (m, 8)
  | .store32 m _ => some (m, 4)
  | .store8 m _ => some (m, 1)
  | .store16 m _ => some (m, 2)
  | .movdquStore m _ => some (m, 16)
  | .vmovdquStore .l128 m _ => some (m, 16)
  | .vmovdquStore .l256 m _ => some (m, 32)
  | .vmovdqu32Store m _ => some (m, 64)
  | .evStore m _ | .e5ExtractStore m _ _ => some (m, 32)
  | .stmxcsr m => some (m, 4)
  | _ => none

/-- Whether an instruction may write memory: those of `storeW`, and the
masked stores. -/
def writesMem (i : Instr) : Bool :=
  (storeW i).isSome || match i with
    | .kStore .. | .kStore8 .. => true
    | _ => false

end RTaint

/-! ## MXCSR along a path (`ScrubOr.lean`) -/

namespace RScrub.Mx

open VG.X86_64.RTaint (storeW writesMem)

/-- A fact two runs agree on: the low 32 bits of a register, or the 4 bytes
at `d` from a register. -/
inductive F where
  | reg (r : Reg)
  | slot (b : Reg) (d : Int)
  deriving DecidableEq

/-- An operand without an index, with a displacement of 32 bits. -/
def plain (m : MemOp) : Bool := m.index.isNone && decide (-2 ^ 31 ≤ m.disp ∧ m.disp < 2 ^ 31)

def slotOf (m : MemOp) : F := .slot m.base m.disp

/-- Whether a fact survives `i`: it writes neither the register nor (or its
base register) the bytes. -/
def keep (i : Instr) : F → Bool
  | .reg r => !Taint.clobbers i r
  | .slot b d => !Taint.clobbers i b && match storeW i with
    | some (m, w) => plain m && m.base == b && decide (w ≤ 64) && decide (-2 ^ 31 ≤ d ∧ d < 2 ^ 31) &&
        decide (m.disp + w ≤ d ∨ d + 4 ≤ m.disp)
    | none => !writesMem i

/-- The facts `i` establishes, given `fs` before it. -/
def adds (fs : List F) : Instr → List F
  | .stmxcsr m => if plain m then [slotOf m] else []
  | .mov32 r (.imm _) => [.reg r]
  | .mov32 r (.mem m) => if plain m && fs.contains (slotOf m) then [.reg r] else []
  | .alu32 .and r (.imm _) => if fs.contains (.reg r) then [.reg r] else []
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

/-- The facts after `c`, given `fs` before it, if every `ldmxcsr` in it
loads bytes agreed on. A loop's are those after its body from some of `fs`
that its body keeps: `fs`, less what an iteration and then another drop, or
none. -/
def mx : Prog isa → List F → Option (List F)
  | .block is, fs => blk fs is
  | .seq x y, fs => (mx x fs).bind (mx y)
  | .ite _ t e, fs =>
    match mx t fs, mx e fs with
    | some a, some b => some (a.filter b.contains)
    | _, _ => none
  | .loop b _, fs =>
    match mx b fs with
    | none => none
    | some g₁ =>
      match mx b (fs.filter g₁.contains) with
      | none => none
      | some g₂ =>
        match mx b ((fs.filter g₁.contains).filter g₂.contains) with
        | some g₃ =>
          if ((fs.filter g₁.contains).filter g₂.contains).all g₃.contains then some g₃ else mx b []
        | none => mx b []
  | .call _ b, fs => (mx b (regs fs)).map regs
  | .frame _ b j, fs => (mx b (regs fs)).map fun g => regs (g.filter (keep j))
  | .icall .., _ => none

end RScrub.Mx

/-! ## The vectors' upper halves (`UpperLock.lean`) -/

namespace UpperLock

/-- Whether the upper halves agree after `i`, given whether they agreed before it. -/
def stepI (a : Bool) (i : Instr) : Bool :=
  match i with
  | .vop .vzeroupper => true
  | i => a && i.vecLevel == 0

/-- Whether the upper halves agree after `c`, given whether they agreed before it. -/
def up : Prog isa → Bool → Bool
  | .block is, a => is.foldl stepI a
  | .seq x y, a => up y (up x a)
  | .ite _ t e, a => up t a && up e a
  | .loop b _, a => up b a && up b true
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

end VG.X86_64

/-! ## Stack depth (`Depth.lean`) -/

namespace VG

/-- The bytes of stack a frame's push takes. -/
def X86_64.Instr.frameBytes : X86_64.Instr → Nat
  | .push rs => 8 * rs.length
  | .alloc bytes => bytes
  | _ => 0

/-- The most stack below `rsp` that `c` uses at once, in bytes. -/
def Code.x86_64Depth : Prog X86_64.isa → Nat
  | .block _ => 0
  | .seq a b => max a.x86_64Depth b.x86_64Depth
  | .ite _ t e => max t.x86_64Depth e.x86_64Depth
  | .loop b _ => b.x86_64Depth
  | .call _ b => b.x86_64Depth + 8
  | .frame i b _ => b.x86_64Depth + i.frameBytes
  | .icall _ _ b n => max (b.x86_64Depth + 8) n.x86_64Depth

end VG

/-! ## The level the vector registers are cleared at -/

namespace VG.X86_64

open VG.Impl.Scrub.X86_64 (VecLevel writesVec)

/-- How `scrub` clears the vector registers, as an instruction level. -/
def _root_.VG.Impl.Scrub.X86_64.VecLevel.level : VecLevel → Nat
  | .sse => 0
  | .avx => 1
  | .evex => 2

/-- Whether every instruction of `c`, and of the functions it calls, is at a
`vecLevel` of at most `n`: what the registrations ask of their code
(`Scrub.withScrubAll`), as a function of this module, so that compiled code
runs the pass, and not the interpreter a closure of the registration for
each instruction. -/
@[noinline] def allLevel (n : Nat) (c : Prog isa) : Bool := c.all fun i => decide (i.vecLevel ≤ n)

/-- `allLevel`, of `vecLevelR` (`RScrub.withScrub`, `RScrub.withScrubAllF`). -/
@[noinline] def allLevelR (n : Nat) (c : Prog isa) : Bool := c.all fun i => decide (i.vecLevelR ≤ n)

/-- Whether no instruction of `c`, or of the functions it calls, may write a
vector register (`Scrub.withScrubAll`, `RScrub.withScrubAllF`). -/
@[noinline] def noVecWrite (c : Prog isa) : Bool := c.all fun i => !writesVec i

namespace RScrub

/-- The level `scrub` clears the vector registers at for `code`: `pxor` if
nothing in it writes bits 511:128 of a vector register, else `vpxor`
(`Instr.vecLevelR`: whatever it does to MXCSR, which `withScrub` asks of
separately). -/
def levelFor (code : Prog isa) : VecLevel :=
  if code.all (fun i => decide (i.vecLevelR ≤ VecLevel.sse.level)) then .sse else .avx

/-- The level `scrubRegF` clears the vector registers at for `code`: as
`levelFor`, or `evex` for code that writes `zmm16`–`zmm31`. -/
def levelForE (code : Prog isa) : VecLevel :=
  if code.all (fun i => decide (i.vecLevelR ≤ VecLevel.avx.level)) then levelFor code else .evex

end RScrub

namespace Scrub

/-- The level `scrub` clears the vector registers at for `code`, the lowest
that covers its instructions. -/
def levelAll (code : Prog isa) : VecLevel :=
  if code.all (fun i => decide (i.vecLevel ≤ VecLevel.sse.level)) then .sse
  else if code.all (fun i => decide (i.vecLevel ≤ VecLevel.avx.level)) then .avx else .evex

/-! ## The baseline ISA's callers of AVX code (`ScrubUp.lean`) -/

/-- The functions the tables `ts` name. -/
def tableFns (ts : List (String × List FnTable)) : List String := ts.flatMap fun t => t.2.flatMap (·.fns)

/-- The side conditions of `scrubRegUp` that the emitter evaluates: the
code's instructions are below the level `evex`, its upper halves agree at
the end if they did at the start, and it calls indirectly only the
functions of its tables. -/
def UpOk (code : Prog isa) (tables : List (String × List FnTable)) : Bool :=
  code.all (fun i => decide (i.vecLevel ≤ 1)) && UpperLock.up code true &&
    (UpperLock.inames code).all (fun f => decide (f ∈ tableFns tables))

end Scrub

end VG.X86_64
