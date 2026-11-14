module

public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Impl.Scrub.X86_64
public import VerifiedGarbage.Proof.Framework.CodeOnce

/-!
# The checks of the scrub, compiled (x86-64)

The emitter evaluates the side conditions of the scrub of every x86-64
function (`Scrub.withScrubAll`, `RScrub.withScrub` and the others): the
level of its instructions (`Instr.vecLevel`), whether the vectors' upper
halves agree after it (`UpperLock.up`) and whether its MXCSR does
(`Mx.mx`), each over all of its code. This module, which imports only the
trusted base and `CodeOnce`, holds their definitions, so that it can be
compiled (the library `NativeScrubX86_64`, `lakefile.toml`) and the emitter
run them as compiled code, an order of magnitude faster than in the
interpreter. What they mean is proven of them where it was: in
`ResidueKeep.lean`, `UpperLock.lean` and `ScrubOr.lean`.
-/

@[expose] public section

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

namespace VG.X86_64

/-- Whether an instruction loads MXCSR. -/
def loadsMxcsr : Instr → Bool
  | .ldmxcsr _ => true
  | _ => false

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

/-- An instruction's level: see the module docs of `ResidueKeep.lean`. -/
def Instr.vecLevel : Instr → Nat
  | .vop _ | .vmovdquLoad .. | .vmovdquTbl .. | .vbroadcasti128 .. | .vbinLoad ..
  | .vpmadd52Load .. | .zop _ | .vmovdqu32Load .. | .vbroadcasti32x4 .. | .zbcst ..
  | .vpbroadcastdZ .. | .zbcstd .. | .kLoad .. | .kLoad8 .. => 1
  | .vbroadcasti32x4H .. | .eop _ | .evLoad .. | .evMadd52Load .. | .ldmxcsr _
  | .e5op _ | .evBroadcastLoad .. | .e5InsertLoad .. => 2
  | _ => 0

/-- The level of the vector registers alone: `vecLevel`, but `ldmxcsr`,
which writes only MXCSR, at level 0. -/
def Instr.vecLevelR (i : Instr) : Nat := if loadsMxcsr i then 0 else i.vecLevel

/-- Whether `i` is at a level of at most `k`. -/
def Instr.levelLe (k : Nat) (i : Instr) : Bool := decide (i.vecLevel ≤ k)

/-- Whether `i` is at a level of the vector registers of at most `k`. -/
def Instr.levelLeR (k : Nat) (i : Instr) : Bool := decide (i.vecLevelR ≤ k)

/-- Whether every instruction of `c` is at a level of at most `k`
(`Code.allOnce`). -/
def levelLeOnce (k : Nat) (c : Prog isa) : Bool := c.allOnce (Instr.levelLe k)

/-- Whether every instruction of `c` is at a level of the vector registers of
at most `k` (`Code.allOnce`). -/
def levelLeROnce (k : Nat) (c : Prog isa) : Bool := c.allOnce (Instr.levelLeR k)

/-- Whether no instruction of `c` may write a vector register. -/
def noVec (c : Prog isa) : Bool := c.all fun i => !Impl.Scrub.X86_64.writesVec i

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

/-- `up c a`, given calls with `up`'s answer for them (`k`: a call's
function, code, start and answer), with those calls and the calls of `c`:
`up` follows the code of a function once per call of it, through every
function that calls it, and this once per start (`Code.memoCall`). -/
def upFrom : Prog isa → Bool → List (String × Prog isa × Bool × Bool) →
    Bool × List (String × Prog isa × Bool × Bool)
  | .block is, a, k => (is.foldl stepI a, k)
  | .seq x y, a, k =>
    let r := upFrom x a k
    upFrom y r.1 r.2
  | .ite _ t e, a, k =>
    let r := upFrom t a k
    let q := upFrom e a r.2
    (r.1 && q.1, q.2)
  | .loop b _, a, k => upFrom b a k
  | .call n b, a, k => Code.memoCall n b a k fun _ => upFrom b a k
  | .frame _ b _, a, k => upFrom b a k
  | .icall _ n b nx, a, k =>
    let r := Code.memoCall n b a k fun _ => upFrom b a k
    let q := upFrom nx a r.2
    (r.1 && q.1, q.2)

/-- `up c a`, following the code of each function `c` calls once per start. -/
def upOnce (c : Prog isa) (a : Bool) : Bool := (upFrom c a []).1

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
the same function of MXCSR on entry (see the module docs). -/
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

namespace RScrub

/-- `mxClass c`, given calls with their class (`k`: a call's function, code
and class), with those calls and the calls of `c`: `mxClass` follows the
code of a function once per call of it, through every function that calls
it, and this once (`Code.memoCall`). -/
def mxClassFrom : Prog isa → List (String × Prog isa × Unit × Option MxC) →
    Option MxC × List (String × Prog isa × Unit × Option MxC)
  | .block is, k => (if is.all (fun i => !loadsMxcsr i) then some .keep else none, k)
  | .seq a b, k =>
    if restoresC a b then (some .mask, k) else
    let r := mxClassFrom a k
    match r.1 with
    | some x =>
      let q := mxClassFrom b r.2
      (match q.1 with
      | some y => (some (x.comp y), q.2)
      | none => (none, q.2))
    | none => (none, r.2)
  | .ite _ t e, k =>
    let r := mxClassFrom t k
    match r.1 with
    | some x =>
      let q := mxClassFrom e r.2
      (match q.1 with
      | some y => (if x = y then some x else none, q.2)
      | none => (none, q.2))
    | none => (none, r.2)
  | .loop b _, k => mxClassFrom b k
  | .call n b, k => Code.memoCall n b () k fun _ => mxClassFrom b k
  | .frame i b j, k => if !loadsMxcsr i && !loadsMxcsr j then mxClassFrom b k else (none, k)
  | .icall i n b nx, k =>
    if loadsMxcsr i then (none, k) else
    let r := Code.memoCall n b () k fun _ => mxClassFrom b k
    match r.1 with
    | some x =>
      let q := mxClassFrom nx r.2
      (match q.1 with
      | some y => (if x = y then some x else none, q.2)
      | none => (none, q.2))
    | none => (none, r.2)

/-- `mxClass c`, following the code of each function `c` calls once. -/
def mxClassOnce (c : Prog isa) : Option MxC := (mxClassFrom c []).1

end RScrub

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

/-- `mx c fs`, given calls with `mx`'s answer for them (`k`: a call's
function, code, the facts before it and the answer), with those calls and
the calls of `c`: `mx` follows the code of a function once per call of it,
through every function that calls it, and this once for the same facts
(`Code.memoCall`). -/
def mxFrom : Prog isa → List F → List (String × Prog isa × List F × Option (List F)) →
    Option (List F) × List (String × Prog isa × List F × Option (List F))
  | .block is, fs, k => (blk fs is, k)
  | .seq x y, fs, k =>
    let r := mxFrom x fs k
    match r.1 with
    | some g => mxFrom y g r.2
    | none => (none, k)
  | .ite _ t e, fs, k =>
    let r := mxFrom t fs k
    match r.1 with
    | some a =>
      let q := mxFrom e fs r.2
      (match q.1 with
      | some b => (some (a.filter b.contains), q.2)
      | none => (none, k))
    | none => (none, k)
  | .loop b _, fs, k =>
    let r := mxFrom b (fs.filter (kept · b)) k
    match r.1 with
    | some g => (if (fs.filter (kept · b)).all g.contains then some g else none, r.2)
    | none => (none, k)
  | .call n b, fs, k =>
    let r := Code.memoCall n b (regs fs) k fun _ => mxFrom b (regs fs) k
    (r.1.map regs, r.2)
  | .frame _ b j, fs, k =>
    let r := mxFrom b (regs fs) k
    (r.1.map fun g => regs (g.filter (keep j)), r.2)
  | .icall .., _, k => (none, k)

/-- `mx c fs`, following the code of each function `c` calls once for the
same facts. -/
def mxOnce (c : Prog isa) (fs : List F) : Option (List F) := (mxFrom c fs []).1

end RScrub.Mx

end VG.X86_64
