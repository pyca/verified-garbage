module

public import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Framework.NativeHintOps
public import VerifiedGarbage.TCB.X86_64.Target

/-!
# The x86-64 taint analysis, in compiled code

Executable copies of the operations of the x86-64 analysis `X86_64.taint`
(`Proof/Framework/X86_64/Taint.lean`: its `T`, `step`, `meet`, `le` and calls),
separated from their soundness proofs so that the hint search of
`native_taint_decide` runs compiled (`NativeHintSearch`) rather than in the
interpreter. Untrusted: `Taint.check` checks every hint the search finds, with
the analysis itself.

They are the definitions of `X86_64/Taint.lean`, copied: the checked
analysis's `step` is `stepKD`, which agrees with `step` (`stepKD_spec`). A
change to one is a change to the other. `step` matches every instruction, with
no default case, so an instruction added to the ISA model does not compile here
until it has a step (rather than giving the search a weaker one).
-/

@[expose] public section

namespace VG.NativeHints.X86_64
open VG.X86_64

deriving instance Lean.ToExpr for Reg

instance : RegIdx Reg := ⟨Reg.ctorIdx, fun {a b} h => by rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]⟩

deriving instance Lean.ToExpr for XReg

instance : RegIdx XReg := ⟨XReg.ctorIdx, fun {a b} h => by rw [← XReg.ofNat_ctorIdx a, h, XReg.ofNat_ctorIdx]⟩

structure T where
  regs : RegSet Reg
  flags : Bool
  /-- Lower bounds on the lengths of the writable regions `s.wr`, in order (one per region;
  `0` if unknown); `[]` if nothing is known about the regions. -/
  lens : List Nat := []
  /-- `(r, i, k)`: register `r` holds the address of byte `k` of writable region `i`. -/
  bases : List (Reg × Nat × Nat) := []
  /-- `(i, o, n)`: the `n` bytes at offset `o` of writable region `i` are public. -/
  slots : List (Nat × Nat × Nat) := []
  /-- Registers whose low 32 bits are public (a public 32-bit argument, whose
  upper half is whatever the caller left there). Only stores keep them. -/
  lo : RegSet Reg := .empty
  /-- SSE registers known to be public: written by `movq xmm, r64` from a
  public register. Any other write to the vector registers forgets them. -/
  xregs : RegSet XReg := .empty
  deriving DecidableEq, Lean.ToExpr

def pub (τ : T) (r : Reg) : Bool := τ.regs.mem r

def xpub (τ : T) (r : XReg) : Bool := τ.xregs.mem r

/-- `τ` after a write to the vector registers other than `movq xmm, r64`. It
does not look at `τ`, so the kernel does no more work on vector code than
before SSE registers were tracked. -/
def noX (τ : T) : T := match τ with | ⟨rg, f, l, b, sl, lo, _⟩ => ⟨rg, f, l, b, sl, lo, .empty⟩

/-- The public registers after writing `r`, with a public value iff `p`. -/
def set (τ : T) (r : Reg) (p : Bool) : RegSet Reg :=
  if p then τ.regs.insert r else τ.regs.erase r

/-- The public SSE registers after writing `r`, with a public value iff `p`. -/
def setX (τ : T) (r : XReg) (p : Bool) : RegSet XReg :=
  if p then τ.xregs.insert r else τ.xregs.erase r

/-- The known region bases after writing `d`. -/
def kill (τ : T) (d : Reg) : List (Reg × Nat × Nat) := τ.bases.filter (·.1 != d)

def memPub (τ : T) (m : MemOp) : Bool :=
  pub τ m.base && match m.index with
    | none => true
    | some i => pub τ i

/-- The region and offset addressed by `m`, if known. -/
def addrOf (τ : T) (m : MemOp) : Option (Nat × Nat) :=
  if m.index = none ∧ 0 ≤ m.disp then
    (τ.bases.find? (·.1 == m.base)).map fun p => (p.2.1, p.2.2 + m.disp.toNat)
  else none

/-- `w` bytes at `m` are within a public slot. -/
def slotPub (τ : T) (m : MemOp) (w : Nat) : Bool :=
  match addrOf τ m with
  | some (i, d) => τ.slots.any fun sl => sl.1 == i && sl.2.1 ≤ d && d + w ≤ sl.2.1 + sl.2.2
  | none => false

/-- The addresses the operand accesses are public. -/
def srcOk (τ : T) : Src → Bool
  | .mem m => memPub τ m
  | _ => true

/-- The operand's value is public (memory operands aside). -/
def srcPub (τ : T) : Src → Bool
  | .reg r => pub τ r
  | .imm _ => true
  | .mem _ => false

/-- The operand is a register whose low 32 bits are public. -/
def loPub (τ : T) : Src → Bool
  | .reg r => τ.lo.mem r
  | _ => false

/-- A `w`-byte memory operand reads a public slot. -/
def loadPub (τ : T) (w : Nat) : Src → Bool
  | .mem m => slotPub τ m w
  | _ => false

/-- The known region bases after `mov d, src`. -/
def movBases (τ : T) (d : Reg) : Src → List (Reg × Nat × Nat)
  | .reg r => kill τ d ++ (τ.bases.filter (·.1 == r)).map fun p => (d, p.2)
  | _ => kill τ d

/-- The public slots after storing `w` bytes at `m`, a public value iff `p`. -/
def storeSlots (τ : T) (m : MemOp) (w : Nat) (p : Bool) : List (Nat × Nat × Nat) :=
  match addrOf τ m with
  | some (i, d) =>
    if d + w ≤ τ.lens.getD i 0 then
      let kept := τ.slots.filter fun sl => p || sl.1 != i || d + w ≤ sl.2.1 || sl.2.1 + sl.2.2 ≤ d
      if p then (i, d, w) :: kept else kept
    else if p then τ.slots else []
  | none => if p then τ.slots else []

def storeStep (τ : T) (m : MemOp) (w : Nat) (p : Bool) : Option T :=
  if memPub τ m then some { τ with slots := storeSlots τ m w p } else none

def usesCarry : AluOp → Bool
  | .adc | .sbb => true
  | _ => false

def writes : AluOp → Bool
  | .cmp | .test => false
  | _ => true

/-- The known region bases after `op d, src`: a 64-bit `add` of a
non-negative immediate moves a pointer that far into its region, and a `sub`
moves it back (no further back than the region's base). -/
def aluBases (τ : T) (op : AluOp) (d : Reg) (src : Src) (wide : Bool) : List (Reg × Nat × Nat) :=
  match op, src with
  | .add, .imm v =>
    if wide && !v.msb then kill τ d ++ (τ.bases.filter (·.1 == d)).map fun p => (d, p.2.1, p.2.2 + v.toNat)
    else kill τ d
  | .sub, .imm v =>
    if wide && !v.msb then
      kill τ d ++ (τ.bases.filter fun p => p.1 == d && v.toNat ≤ p.2.2).map fun p => (d, p.2.1, p.2.2 - v.toNat)
    else kill τ d
  | _, _ => kill τ d

def aluStep (τ : T) (op : AluOp) (d : Reg) (src : Src) (wide : Bool) : Option T :=
  if srcOk τ src then
    let p := pub τ d && srcPub τ src && (!usesCarry op || τ.flags)
    some { τ with
      regs := if writes op then set τ d p else τ.regs, flags := p, bases := aluBases τ op d src wide, lo := .empty }
  else none

/-- `mul r`: `rax`, `rdx` and the flags are functions of the old `rax` and
`r` (SF and ZF become undefined in both runs). -/
def mulStep (τ : T) (r : Reg) : T :=
  let p := pub τ .rax && pub τ r
  { τ with regs := if p then (τ.regs.insert .rax).insert .rdx else (τ.regs.erase .rax).erase .rdx,
           flags := p, bases := (kill τ .rax).filter (·.1 != .rdx), lo := .empty }

/-- `mulx hi, lo, src`: `hi` and `lo` are functions of `rdx` and `src`; the
flags are unchanged. -/
def mulxStep (τ : T) (hi lo : Reg) (src : Src) : T :=
  let p := pub τ .rdx && srcPub τ src
  { τ with regs := if p then (τ.regs.insert lo).insert hi else (τ.regs.erase lo).erase hi,
           bases := (kill τ hi).filter (·.1 != lo), lo := .empty }

/-- `adcx d, src` and `adox d, src`: `d` and the flag it changes are
functions of `d`, `src` and that flag. -/
def adxStep (τ : T) (d : Reg) (src : Src) : Option T :=
  if srcOk τ src then
    let p := pub τ d && srcPub τ src && τ.flags
    some { τ with regs := set τ d p, flags := p, bases := kill τ d, lo := .empty }
  else none

/-- `cmovcc d, src`: `d` is a function of its old value, of `src` (read
whether or not the condition holds, from a public slot or not) and of the
flag the condition reads; the flags are unchanged. -/
def cmovStep (τ : T) (d : Reg) (src : Src) : Option T :=
  if srcOk τ src then
    let p := pub τ d && (srcPub τ src || loadPub τ 8 src) && τ.flags
    some { τ with regs := set τ d p, bases := kill τ d, lo := .empty }
  else none

def step (τ : T) : Instr → Option T
  | .mov d src =>
    if srcOk τ src then
      some { τ with regs := set τ d (srcPub τ src || loadPub τ 8 src), bases := movBases τ d src, lo := .empty }
    else none
  | .mov32 d src =>
    if srcOk τ src then
      some { τ with
        regs := set τ d (srcPub τ src || loadPub τ 4 src || loPub τ src), bases := kill τ d, lo := .empty }
    else none
  | .store m r => storeStep τ m 8 (pub τ r)
  | .store32 m r => storeStep τ m 4 (pub τ r)
  | .store8 m r => storeStep τ m 1 (pub τ r)
  | .alu op d src => aluStep τ op d src true
  | .alu32 op d src => aluStep τ op d src false
  -- The result is a function of the old value of `d`, and so are the
  -- flags that change.
  | .shift32 _ d _ | .shift _ d _ =>
    some { τ with flags := τ.flags && pub τ d, bases := kill τ d, lo := .empty }
  | .bswap32 d | .bswap d => some { τ with bases := kill τ d, lo := .empty }
  -- `rorx` changes no flag; `andn` sets them from its result.
  | .rorx32 d r _ | .rorx d r _ => some { τ with regs := set τ d (pub τ r), bases := kill τ d, lo := .empty }
  | .andn32 d a b | .andn d a b =>
    let p := pub τ a && pub τ b
    some { τ with regs := set τ d p, flags := p, bases := kill τ d, lo := .empty }
  -- `imul` sets CF and OF from its operands, and leaves ZF and SF undefined.
  | .imul d r =>
    let p := pub τ d && pub τ r
    some { τ with regs := set τ d p, flags := p, bases := kill τ d, lo := .empty }
  | .movImm64 d _ => some { τ with regs := set τ d true, bases := kill τ d, lo := .empty }
  -- The analysis does not track the addresses of statics.
  | .leaSym d _ => some { τ with regs := set τ d false, bases := kill τ d, lo := .empty }
  | .movzx8 d m =>
    if memPub τ m then some { τ with regs := set τ d false, bases := kill τ d, lo := .empty } else none
  -- The vector registers are secret but for those `movq xmm, r64` wrote
  -- from a public register (`xregs`): what `vpmovmskb` moves from one into a
  -- general-purpose register is secret, and no modelled instruction moves
  -- them into the flags.
  | .vpmovmskb _ d _ => some { τ with regs := set τ d false, bases := kill τ d, lo := .empty }
  | .movqR d r => some { τ with regs := set τ d (xpub τ r), bases := kill τ d, lo := .empty }
  | .movdquLoad _ m => if memPub τ m then some (noX τ) else none
  | .movdquStore m _ => storeStep τ m 16 false
  | .xop (.movq d r) => some { τ with xregs := setX τ d (pub τ r) }
  | .xop _ | .vop _ => some (noX τ)
  | .vmovdquLoad _ _ m | .vbroadcasti128 _ m | .vbinLoad _ _ _ _ m => if memPub τ m then some (noX τ) else none
  | .vmovdquStore .l128 m _ => storeStep τ m 16 false
  | .vmovdquStore .l256 m _ => storeStep τ m 32 false
  | .zop _ => some (noX τ)
  | .vmovdqu32Load _ m | .vbroadcasti32x4 _ m | .vbroadcasti32x4H _ m | .zbcst _ _ _ m | .vpmadd52Load _ _ _ m =>
    if memPub τ m then some (noX τ) else none
  | .vmovdqu32Store m _ => storeStep τ m 64 false
  | .eop _ => some (noX τ)
  | .evLoad _ m | .evMadd52Load _ _ _ m => if memPub τ m then some (noX τ) else none
  | .evStore m _ => storeStep τ m 32 false
  -- A masked move accesses the quadwords its mask enables, which must be
  -- public as its address is.
  | .kLoad k _ m => if memPub τ m && pub τ k then some (noX τ) else none
  | .kStore m k _ => if pub τ k then storeStep τ m 64 false else none
  -- MXCSR is not tracked either: nothing moves it into a general-purpose
  -- register or the flags, and it is stored as a secret.
  | .stmxcsr m => storeStep τ m 4 false
  | .ldmxcsr m => if memPub τ m then some τ else none
  | .lfence => some τ
  | .mul r => some (mulStep τ r)
  | .mulx hi lo src => if srcOk τ src then some (mulxStep τ hi lo src) else none
  | .adcx d src | .adox d src => adxStep τ d src
  | .cmov _ d src => cmovStep τ d src
  -- Frames are not analysed.
  | .push _ | .pop .. | .alloc _ | .free _ => none

def meet (τ₁ τ₂ : T) : T where
  regs := τ₁.regs.inter τ₂.regs
  flags := τ₁.flags && τ₂.flags
  lens := if τ₁.lens = τ₂.lens then τ₁.lens else []
  bases := τ₁.bases.filter (τ₂.bases.contains ·)
  slots := if τ₁.lens = τ₂.lens then τ₁.slots.filter (τ₂.slots.contains ·) else []
  lo := τ₁.lo.inter τ₂.lo
  xregs := τ₁.xregs.inter τ₂.xregs

def le (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && τ.lens == σ.lens &&
    τ.bases.all (σ.bases.contains ·) && τ.slots.all (σ.slots.contains ·) && τ.lo.subset σ.lo &&
    τ.xregs.subset σ.xregs

def callStep (τ : T) : Option T :=
  if pub τ .rsp then some { τ with bases := kill τ .rsp, slots := [], lo := .empty } else none

/-- A return loads its return address from `[rsp]` and moves `rsp`. -/
def retStep (τ : T) : Option T :=
  if pub τ .rsp then some { τ with bases := kill τ .rsp, lo := .empty } else none

def hintOps : VG.NativeHintOps isa where
  T := T
  step := step
  condPub τ _ := τ.flags
  meet := meet
  le := le
  call := callStep
  ret := retStep
  push _ _ := none
  pop _ _ := none

end VG.NativeHints.X86_64

namespace VG.NativeHints.X86_64.provider
/-- An untrusted native hint; `Taint.check` still checks every interval. -/
def hintOfSize := VG.NativeHintOps.hintOfSize VG.NativeHints.X86_64.hintOps
def hintWeakOfSize := VG.NativeHintOps.hintWeakOfSize VG.NativeHints.X86_64.hintOps
end VG.NativeHints.X86_64.provider
