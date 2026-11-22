module

public import VerifiedGarbage.Proof.Framework.TaintCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
public meta import VerifiedGarbage.Proof.Framework.TaintCT
public meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# What a function leaves in its registers and on its stack (x86, 32-bit)

`rtaint` is a taint analysis for two runs that leak the same (`TaintCT`) of
code whose stack is the `W` bytes below the stack pointer on entry (its
*window*), as ARMv7's (`Proof/Framework/Arm/ResidueTaint.lean`). It follows
what the code puts on the stack (`stk`, from the stack pointer up): the
frames it opens (`alloc`, `push` of registers, the four bytes of `symPush`,
an MCDT frame) and the return addresses of its calls, which are nested in
the window from its top down, and keeps, as a bit mask, the bytes of the
window that may differ between the two runs (`sec`). What it knows of the
registers, the flags and the arguments:

* whether a register holds the same value in both runs (`pub`), whether the
  flags CF, ZF, SF and OF do and are defined (`fl`), and which XMM registers
  hold the same value in both runs (`px`, a bit mask);
* whether a register holds the address of byte `k` of the window (`wp`), as
  `esp` does of byte `sp`: a store through it then writes bytes the analysis
  knows, and a load through it reads them, public if they are;
* the `an` bytes of arguments above the return address on entry (at byte
  `W + 4` on), which hold the same in both runs while `ak` holds: a load
  of them is public, and a store of a secret there, or one the analysis
  cannot place, clears `ak` (the arguments are writable if the contract
  lets the function overwrite them).

The model faults on a store that is not within one writable region, which
are the frames, the buffers and (if writable) the arguments: a store the
analysis cannot place is in a frame still open, or in one of the others, so
a secret stored there makes only the bytes of the open frames secret (`sec`
from the stack pointer up), and the arguments unknown. A push makes its
frame's bytes public if every register it stores is, and secret otherwise;
a call's return address, and the word `symPush` stores, are the state's next
unknown, which the two runs share, so public. The bytes of a frame the code
releases are what it left there, or what replaces them (`lose`), which the
two runs' unknowns, shared, decide alike.

The analysis has no case for an indirect call (`TaintCT.check` has none) and
none for an MMX instruction or frame: such code is not analysed, and keeps
`scrubAll`. An instruction that writes `esp` (other than as the push or pop
of a frame) stops it too.

`ResidueTaintSound.lean` proves it sound.
-/

@[expose] public section

namespace VG.X86.RTaint

open VG.X86

/-! ## Sets of bytes as bit masks -/

/-- The `w` low bits. -/
def ones (w : Nat) : Nat := Nat.sub (Nat.pow 2 w) 1

/-- `b` with its `w` bits from bit `d` set. -/
def bset (b d w : Nat) : Nat := Nat.lor b (Nat.shiftLeft (ones w) d)

/-- `b` with its `w` bits from bit `d` cleared. -/
def bclr (b d w : Nat) : Nat := Nat.xor b (Nat.land b (Nat.shiftLeft (ones w) d))

/-- None of the `w` bits of `b` from bit `d` is set. -/
def bnone (b d w : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight b d) (ones w)) 0

/-- Every bit of `a` is set in `b`. -/
def bsub (a b : Nat) : Bool := Nat.beq (Nat.land a b) a

/-! ## The stack

An item of `stk` is the length of its writable region: a frame of `n` bytes
(`n`, a positive multiple of 4), a return address (`0`, four bytes in no
region) or an MCDT frame (`9`: twelve bytes, the region its nine low ones). -/

/-- The bytes of the stack an item of `stk` takes. -/
def size (n : Nat) : Nat := if n = 0 then 4 else if n = 9 then 12 else n

/-- The index of an XMM register, its bit in `px`. -/
def xidx : XReg → Nat
  | .xmm0 => 0 | .xmm1 => 1 | .xmm2 => 2 | .xmm3 => 3
  | .xmm4 => 4 | .xmm5 => 5 | .xmm6 => 6 | .xmm7 => 7

/-- The XMM register an SSE instruction writes. -/
def xdst : XOp → XReg
  | .bin _ d _ | .shift _ d _ | .pshufd d .. | .pshuflw d .. | .pshufhw d .. | .palignr d ..
  | .sha256rnds2 d _ | .sha1rnds4 d .. | .movd d _ | .aeskeygenassist d .. | .pclmulqdq d .. => d

/-- `pxor x, x`, which zeroes `x` whatever it held. -/
def xzero : XOp → Bool
  | .bin .pxor d r => Nat.beq (xidx d) (xidx r)
  | _ => false

/-! ## The analysis -/

/-- What the analysis knows (see the module's documentation). `ok` false
knows nothing: where two paths meet with different stacks. -/
structure T where
  ok : Bool
  W : Nat
  an : Nat
  ak : Bool
  pub : RegSet Reg
  fl : Bool
  px : Nat
  sp : Nat
  stk : List Nat
  wp : List (Reg × Nat)
  sec : Nat
  deriving Lean.ToExpr

/-- What knows nothing. -/
def bot : T := ⟨false, 0, 0, false, RegSet.empty, false, 0, 0, [], [], 0⟩

/-- Whether `r` is `esp`, by the registers' indices (for the kernel). -/
def isSp (r : Reg) : Bool := Nat.beq r.ctorIdx Reg.esp.ctorIdx

/-- Whether two registers are the same, by their indices. -/
def regEq (a b : Reg) : Bool := Nat.beq a.ctorIdx b.ctorIdx

/-- The offset into the window `r` holds, if known: `esp`'s is `sp`. -/
def wpOf (τ : T) (r : Reg) : Option Nat :=
  if isSp r then some τ.sp else (τ.wp.find? (fun e => regEq e.1 r)).map (·.2)

def pubR (τ : T) (r : Reg) : Bool := τ.pub.mem r

/-- `x` holds the same value in both runs. -/
def pubX (τ : T) (x : XReg) : Bool := Nat.testBit τ.px (xidx x)

/-- `τ` with `d` written: public iff `p`, the window offset `k` if known. -/
def setR (τ : T) (d : Reg) (p : Bool) (k : Option Nat) : T :=
  { τ with
    pub := if p then τ.pub.insert d else τ.pub.erase d
    wp := (match k with | some k => [(d, k)] | none => []) ++ τ.wp.filter (fun e => !regEq e.1 d) }

/-- `τ` with the flags public (and defined) iff `p`. -/
def setF (τ : T) (p : Bool) : T := { τ with fl := p }

/-- `τ` with `x` written: the same in both runs iff `p`. -/
def setX (τ : T) (x : XReg) (p : Bool) : T :=
  { τ with px := if p then Nat.lor τ.px (Nat.pow 2 (xidx x)) else bclr τ.px (xidx x) 1 }

/-- `τ` with `n` public (the base register of an access, whose address is
the same in both runs). -/
def withPub (τ : T) (n : Reg) : T := { τ with pub := τ.pub.insert n }

/-- The window offset after subtracting `v`, if not below the window. -/
def offSub (k v : Nat) : Option Nat := if v ≤ k then some (k - v) else none

/-- A load of `w` bytes at `off` from what a register whose window offset is
`k` (if known) holds: public if they are in the window and none of them is
secret, or among the public arguments. -/
def loadPub (τ : T) (k : Option Nat) (off w : Nat) : Bool :=
  match k with
  | some k =>
    (Nat.ble (k + off + w) τ.W && bnone τ.sec (k + off) w) ||
      (τ.ak && Nat.ble (τ.W + 4) (k + off) && Nat.ble (k + off + w) (τ.W + 4 + τ.an))
  | none => false

/-- The bytes of the frames open made secret, and the arguments unknown. -/
def framesSec (τ : T) : T := { τ with sec := bset τ.sec τ.sp (τ.W - τ.sp), ak := false }

/-- A store of `w` bytes at offset `off` from what a register with window
offset `k` (if known) holds, of a value public iff `p`. -/
def storeT (τ : T) (k : Option Nat) (off w : Nat) (p : Bool) : T :=
  match k with
  | some k =>
    if Nat.ble (k + off + w) τ.W then
      { τ with sec := if p then bclr τ.sec (k + off) w else bset τ.sec (k + off) w }
    else if Nat.ble (τ.W + 4) (k + off) && Nat.ble (k + off + w) (τ.W + 4 + τ.an) then
      if p then τ else { τ with ak := false }
    else if p then τ else framesSec τ
  | none => if p then τ else framesSec τ

/-- The value a source operand gives is public (a memory source, through its
base register's window offset). -/
def srcPub (τ : T) : Src → Bool
  | .reg r => pubR τ r
  | .imm _ => true
  | .mem m => loadPub τ (wpOf τ m.base) m.disp 4

/-- `xor d, d` or `sub d, d`: zero, with flags of zero, whatever `d` held. -/
def zeroIdiom (op : AluOp) (d : Reg) : Src → Bool
  | .reg r => (match op with | .xor | .sub => true | _ => false) && regEq r d
  | _ => false

/-- An ALU instruction's step. -/
def aluT (τ : T) (op : AluOp) (d : Reg) (src : Src) : T :=
  if zeroIdiom op d src then setF (setR τ d true none) true
  else
    match op, src with
    | .add, .imm v =>
      let p := pubR τ d
      setF (setR τ d p ((wpOf τ d).map (· + v.toNat))) p
    | .sub, .imm v =>
      let p := pubR τ d
      setF (setR τ d p ((wpOf τ d).bind (offSub · v.toNat))) p
    | _, _ =>
      let p := pubR τ d && srcPub τ src && (!Taint.usesCarry op || τ.fl)
      if Taint.writes op then setF (setR τ d p none) p else setF τ p

/-- An instruction's step, its base register (if it accesses memory) public. -/
def stepB (τ : T) : Instr → Option T
  | .mov d src =>
    if isSp d then none
    else match src with
      | .reg r => some (setR τ d (pubR τ r) (wpOf τ r))
      | _ => some (setR τ d (srcPub τ src) none)
  | .store m r => some (storeT τ (wpOf τ m.base) m.disp 4 (pubR τ r))
  | .alu op d src => if isSp d then none else some (aluT τ op d src)
  | .shift _ d n =>
    if isSp d then none
    else let p := pubR τ d; some (setF (setR τ d p none) (τ.fl && p && Nat.beq n 1))
  | .bswap d => if isSp d then none else some (setR τ d (pubR τ d) none)
  | .movzx8 d m => if isSp d then none else some (setR τ d (loadPub τ (wpOf τ m.base) m.disp 1) none)
  | .store8 m r => some (storeT τ (wpOf τ m.base) m.disp 1 (pubR τ r.reg))
  | .mul r =>
    let p := pubR τ .eax && pubR τ r
    some (setF (setR (setR τ .eax p none) .edx p none) false)
  | .movdquLoad d _ | .movqLoad d _ | .pmuludq d _ => some (setX τ d false)
  -- The words of a table an instruction carries: the same in both runs.
  | .movdquTbl d .. | .movqTbl d .. => some (setX τ d true)
  | .movdquStore m x => some (storeT τ (wpOf τ m.base) m.disp 16 (pubX τ x))
  | .movqStore m x => some (storeT τ (wpOf τ m.base) m.disp 8 (pubX τ x))
  | .xop op => some (setX τ (xdst op) (xzero op))
  | .symPush .. | .push _ | .pop .. | .alloc _ | .free _ | .callr _ | .mop _ | .mmxStore .. | .mmxEnter
  | .emms | .mcdtEnter _ | .mcdtLeave => none

/-- The base register of an access to memory. -/
def base : Instr → Option Reg
  | .mov _ (.mem m) | .alu _ _ (.mem m) | .store m _ | .movzx8 _ m | .store8 m _ | .movdquLoad _ m
  | .movdquStore m _ | .movqLoad _ m | .movqStore m _ => some m.base
  | _ => none

def step (τ : T) (i : Instr) : Option T :=
  if τ.ok then
    match base i with
    | some n => stepB (withPub τ n) i
    | none => stepB τ i
  else none

/-- `τ` with an item `n` of `b` bytes below the others, the window's bytes
that may differ being `sec`. -/
def opened (τ : T) (n b : Nat) (sec : Nat) : T := { τ with sp := τ.sp - b, stk := n :: τ.stk, sec := sec }

/-- A frame of `b` bytes, below the others; of the registers `rs` (`push`),
whose bytes are public if every one of them is; of `symPush`'s word, public
(the next unknown), its register secret (`syms` is not compared); or an
MCDT frame, whose two words it stores are public. -/
def push (τ : T) : Instr → Option T
  | .alloc b =>
    if τ.ok && Nat.ble b τ.sp && Nat.beq (b % 4) 0 && Nat.blt 0 b then some (opened τ b b τ.sec) else none
  | .push rs =>
    let n := 4 * rs.length
    if τ.ok && Nat.ble n τ.sp && Nat.blt 0 n then
      some (opened τ n n (if rs.all (pubR τ) then bclr τ.sec (τ.sp - n) n else bset τ.sec (τ.sp - n) n))
    else none
  | .symPush d _ =>
    if τ.ok && !isSp d && Nat.ble 4 τ.sp then
      some (setF (setR (opened τ 4 4 (bclr τ.sec (τ.sp - 4) 4)) d false none) false)
    else none
  | .mcdtEnter r =>
    if τ.ok && !isSp r && Nat.ble 12 τ.sp then
      some (setR (opened τ 9 12 (bclr τ.sec (τ.sp - 12) 8)) r true none)
    else none
  | _ => none

/-- `τ` with its innermost item, of `b` bytes, released. -/
def close (τ : T) (b : Nat) : T := { τ with sp := τ.sp + b, stk := τ.stk.tail }

/-- The innermost item of `stk` is `n`, which fits below the window's top. -/
def topIs (τ : T) (n : Nat) : Bool :=
  τ.ok && (match τ.stk with | m :: _ => Nat.beq m n | [] => false) && Nat.ble (τ.sp + size n) τ.W

/-- The innermost frame, of `b` bytes, released; of `4 k` bytes, its last
word loaded into `r` (`pop r k`), public if its bytes are; or an MCDT
frame. -/
def pop (τ : T) : Instr → Option T
  | .free b => if topIs τ b && Nat.blt 0 b && Nat.beq (b % 4) 0 then some (close τ b) else none
  | .pop r k =>
    if topIs τ (4 * k) && Nat.blt 0 k && !isSp r then
      some (close (setR τ r (bnone τ.sec (τ.sp + 4 * (k - 1)) 4) none) (4 * k))
    else none
  | .mcdtLeave => if topIs τ 9 then some (close τ 12) else none
  | _ => none

/-- A call: its return address, the next unknown, is public, below the stack. -/
def call (τ : T) : Option T :=
  if τ.ok && Nat.ble 4 τ.sp then some (opened τ 0 4 (bclr τ.sec (τ.sp - 4) 4)) else none

/-- A return, past the return address at the top of the stack. -/
def ret (τ : T) : Option T := if topIs τ 0 then some (close τ 4) else none

/-- Both: what both know, the stacks being the same. -/
def meet (τ σ : T) : T :=
  if τ.ok && σ.ok && Nat.beq τ.W σ.W && Nat.beq τ.an σ.an && Nat.beq τ.sp σ.sp && τ.stk == σ.stk then
    { τ with
      ak := τ.ak && σ.ak
      pub := τ.pub.inter σ.pub
      fl := τ.fl && σ.fl
      px := Nat.land τ.px σ.px
      wp := τ.wp.filter (fun e => !isSp e.1 && wpOf σ e.1 == some e.2)
      sec := Nat.lor τ.sec σ.sec }
  else bot

/-- `τ` knows no more than `σ`. -/
def le (τ σ : T) : Bool :=
  !τ.ok ||
    (σ.ok && Nat.beq τ.W σ.W && Nat.beq τ.an σ.an && Nat.beq τ.sp σ.sp && τ.stk == σ.stk &&
      (!τ.ak || σ.ak) && τ.pub.subset σ.pub && (!τ.fl || σ.fl) && bsub τ.px σ.px &&
      τ.wp.all (fun e => !isSp e.1 && wpOf σ e.1 == some e.2) && bsub σ.sec τ.sec)

/-- Every register. -/
def allRegs : List Reg := [.eax, .ecx, .edx, .ebx, .esp, .ebp, .esi, .edi]

/-- Where the analysis of a function starts, with its window of `W` bytes
and `an` bytes of public arguments: every register and XMM register public,
the flags not known defined, no frame. -/
def init (W an : Nat) : T := ⟨true, W, an, true, RegSet.ofList allRegs, false, 255, W, [], [], 0⟩

/-- Where the analysis of a function must end: every item of the stack
released, no byte of the window secret, `ecx`, the flags and every XMM
register public, and of the result `edx ++ eax` at most its `rb` low bits
secret. -/
def done (rb : Nat) (τ : T) : Bool :=
  τ.ok && τ.stk.isEmpty && Nat.beq τ.sp τ.W && Nat.beq τ.sec 0 && pubR τ .ecx && τ.fl &&
    Nat.beq τ.px 255 && (Nat.ble 64 rb || pubR τ .edx) && (Nat.ble 32 rb || pubR τ .eax)

/-! ## The step the kernel finds again

As on ARMv7 (see "An analysis the kernel finds again" in the
`proof-performance` skill): `stepK` is `step` (`stepK_eq`) giving a taint
whose fields are evaluated (`forceT`), but the mask of the window's bytes, a
numeral wider than 64 bits, which stays the term it was where the step
leaves it the same number (`forceTS`). `stepK` matches on the instruction
once, with its cases closed (`inline_match%`); `callK`, `retK`, `pushK`,
`popK` and `meetK` are `call`, `ret`, `push`, `pop` and `meet`, evaluated
likewise. `rtaint` takes them; the soundness proofs stay about `step` and
the others. -/

/-- `k n`, with the number `n` evaluated. -/
def forceNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  Nat.casesOn (motive := fun _ => α) (Nat.succ n) (k n) (fun m => k m)

theorem forceNat_eq {α : Type} (n : Nat) (k : Nat → α) : forceNat n k = k n := rfl

/-- `k b`, with `b` evaluated. -/
def forceBool {α : Type} (b : Bool) (k : Bool → α) : α :=
  Bool.casesOn (motive := fun _ => α) b (k false) (k true)

theorem forceBool_eq {α : Type} (b : Bool) (k : Bool → α) : forceBool b k = k b := by
  cases b <;> rfl

/-- `k l`, with the list `l` and the number of each of its registers evaluated. -/
def forceRegs {α : Type} : List (Reg × Nat) → (List (Reg × Nat) → α) → α
  | [], k => k []
  | (r, n) :: l, k => forceNat n fun n => forceRegs l fun l => k ((r, n) :: l)

theorem forceRegs_eq {α : Type} (l : List (Reg × Nat)) (k : List (Reg × Nat) → α) :
    forceRegs l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨r, n⟩ := e
    rw [forceRegs, forceNat_eq, ih]

/-- `k l`, with the list of numbers `l` evaluated. -/
def forceNats {α : Type} : List Nat → (List Nat → α) → α
  | [], k => k []
  | n :: l, k => forceNat n fun n => forceNats l fun l => k (n :: l)

theorem forceNats_eq {α : Type} (l : List Nat) (k : List Nat → α) : forceNats l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons n l ih => rw [forceNats, forceNat_eq, ih]

/-- `k τ`, with every field of `τ` evaluated but the mask. -/
def forceT {α : Type} (τ : T) (k : T → α) : α :=
  match τ with
  | ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ =>
    forceBool ok fun ok => forceNat W fun W => forceNat an fun an => forceBool ak fun ak =>
      pub.force fun pub => forceBool fl fun fl => forceNat px fun px => forceNat sp fun sp =>
        forceNats stk fun stk => forceRegs wp fun wp => k ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩

/-- `forceT`, the mask being the term `sec0` if it is that number. -/
def forceTS {α : Type} (sec0 : Nat) (τ : T) (k : T → α) : α :=
  match τ with
  | ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ =>
    Bool.casesOn (motive := fun _ => α) (Nat.beq sec sec0)
      (forceT ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ k)
      (forceT ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec0⟩ k)

theorem forceTS_eq {α : Type} (sec0 : Nat) (τ : T) (k : T → α) : forceTS sec0 τ k = forceT τ k := by
  obtain ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ := τ
  show Bool.casesOn (motive := fun _ => α) (Nat.beq sec sec0)
    (forceT ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ k)
    (forceT ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec0⟩ k) = _
  cases h : Nat.beq sec sec0
  · rfl
  · rw [Nat.eq_of_beq_eq_true h]

theorem forceT_eq {α : Type} (τ : T) (k : T → α) : forceT τ k = k τ := by
  obtain ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ := τ
  rw [forceT, forceBool_eq, forceNat_eq, forceNat_eq, forceBool_eq, RegSet.force_eq, forceBool_eq,
    forceNat_eq, forceNat_eq, forceNats_eq, forceRegs_eq]

/-- `o`, its taint evaluated, the mask being the term `sec0` if it is that number. -/
def forceO (sec0 : Nat) (o : Option T) : Option T :=
  match o with
  | some τ => forceTS sec0 τ some
  | none => none

theorem forceO_eq (sec0 : Nat) (o : Option T) : forceO sec0 o = o := by
  cases o with
  | none => rfl
  | some τ => exact (forceTS_eq sec0 τ some).trans (forceT_eq τ some)

/-- `step`, as a function of the instruction first. -/
def stepFn (i : Instr) : T → Option T := fun τ => step τ i

/-- `stepFn`, with its cases closed (`inline_match%`). -/
def stepFnK : Instr → T → Option T := inline_match% stepFn step stepB base

theorem stepFnK_eq (i : Instr) : stepFnK i = stepFn i := by cases i <;> rfl

/-- `step`, giving a taint that is evaluated. -/
def stepK (τ : T) (i : Instr) : Option T :=
  match τ with
  | ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ =>
    forceO sec (stepFnK i ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩)

theorem stepK_eq (τ : T) (i : Instr) : stepK τ i = step τ i := by
  obtain ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ := τ
  rw [stepK, forceO_eq, stepFnK_eq]
  rfl

/-- `call`, giving a taint that is evaluated. -/
def callK (τ : T) : Option T :=
  match τ with
  | ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ => forceO sec (call ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩)

theorem callK_eq (τ : T) : callK τ = call τ := by
  obtain ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ := τ
  exact forceO_eq _ _

/-- `ret`, giving a taint that is evaluated. -/
def retK (τ : T) : Option T :=
  match τ with
  | ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ => forceO sec (ret ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩)

theorem retK_eq (τ : T) : retK τ = ret τ := by
  obtain ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ := τ
  exact forceO_eq _ _

/-- `push`, giving a taint that is evaluated. -/
def pushK (τ : T) (i : Instr) : Option T :=
  match τ with
  | ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ => forceO sec (push ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ i)

theorem pushK_eq (τ : T) (i : Instr) : pushK τ i = push τ i := by
  obtain ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ := τ
  exact forceO_eq _ _

/-- `pop`, giving a taint that is evaluated. -/
def popK (τ : T) (i : Instr) : Option T :=
  match τ with
  | ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ => forceO sec (pop ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ i)

theorem popK_eq (τ : T) (i : Instr) : popK τ i = pop τ i := by
  obtain ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ := τ
  exact forceO_eq _ _

/-- `meet`, giving a taint that is evaluated. -/
def meetK (τ σ : T) : T :=
  match τ with
  | ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ =>
    forceTS sec (meet ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ σ) id

theorem meetK_eq (τ σ : T) : meetK τ σ = meet τ σ := by
  obtain ⟨ok, W, an, ak, pub, fl, px, sp, stk, wp, sec⟩ := τ
  exact (forceTS_eq _ _ id).trans (forceT_eq _ id)

end VG.X86.RTaint
