module

public import VerifiedGarbage.Proof.Framework.TaintCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public meta import VerifiedGarbage.Proof.Framework.TaintCT
public meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-!
# What a function leaves in its registers and on its stack (ARMv7)

`rtaint` is a taint analysis for two runs that leak the same (`TaintCT`) of
code whose stack is the `W` bytes below the stack pointer on entry (its
*window*), as RISC-V64's (`Proof/Framework/RISCV64/ResidueTaint.lean`). It
follows the frames the code opens (`alloc`, `free`, and `push` of a list of
registers, `pop` of one word), which are nested in the window from its top
down, and keeps, as a bit mask, the bytes of the window that may differ
between the two runs (`sec`). What it knows of the registers and flags:

* whether a register holds the same value in both runs (`pub`), and whether
  the flags N, Z, C and V do (`fl`);
* whether a register holds the address of byte `k` of the window (`wp`): a
  store through it then writes bytes the analysis knows, and a load through
  it reads them, public if they are;
* whether the `room` bytes from the address it holds are outside the window
  (`bp`), as those of a buffer are: a store through it within them leaves the
  window as it was.

The model faults on a store that is not within one writable region (`wr`),
which are the frames and the buffers: a store the analysis cannot place is in
a frame still open, or in a buffer, so a secret stored there makes only the
bytes of the open frames secret (`sec` from the stack pointer up). A `push`
makes its frame's bytes public if every register it stores is, and secret
otherwise. The bytes of a frame the code releases are what it left there, or
what replaces them (`lose`), which the two runs' unknowns, shared, decide
alike. A call leaves the unknowns in `lr`, `r12` and the flags, the same in
both runs: they are public.

The analysis has no case for an indirect call (`TaintCT.check` has none): code
that calls the functions of its tables is not analysed, and keeps `scrubAll`.
The model has no `ldrd` or `strd`.

`ResidueTaintSound.lean` proves it sound.
-/

@[expose] public section

namespace VG.Arm.RTaint

open VG.Arm

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

/-! ## The analysis -/

/-- What the analysis knows (see the module's documentation). `ok` false
knows nothing: where two paths meet with different frames. -/
structure T where
  ok : Bool
  W : Nat
  pub : RegSet Reg
  fl : Bool
  sp : Nat
  nf : Nat
  wp : List (Reg × Nat)
  bp : List (Reg × Nat)
  sec : Nat
  deriving Lean.ToExpr

/-- What knows nothing. -/
def bot : T := ⟨false, 0, RegSet.empty, false, 0, 0, [], [], 0⟩

/-- The offset into the window `r` holds, if known. -/
def wpOf (τ : T) (r : Reg) : Option Nat := (τ.wp.find? (·.1 == r)).map (·.2)

/-- The bytes outside the window from the address `r` holds, if known. -/
def bpOf (τ : T) (r : Reg) : Option Nat := (τ.bp.find? (·.1 == r)).map (·.2)

def pubR (τ : T) (r : Reg) : Bool := τ.pub.mem r

/-- The second operand is the same in both runs. -/
def op2Pub (τ : T) : Op2 → Bool
  | .imm _ => true
  | .reg r => pubR τ r
  | .shifted r _ _ => pubR τ r

/-- `τ` with `d` written: public iff `p`, the window offset `k` and the room
`b` if known. -/
def setR (τ : T) (d : Reg) (p : Bool) (k b : Option Nat) : T :=
  { τ with
    pub := if p then τ.pub.insert d else τ.pub.erase d
    wp := (match k with | some k => [(d, k)] | none => []) ++ τ.wp.filter (·.1 != d)
    bp := (match b with | some b => [(d, b)] | none => []) ++ τ.bp.filter (·.1 != d) }

/-- `τ` with the flags public iff `p`. -/
def setF (τ : T) (p : Bool) : T := { τ with fl := p }

/-- `τ` with `n` public (the base register of an access, whose address is
the same in both runs). -/
def withPub (τ : T) (n : Reg) : T := { τ with pub := τ.pub.insert n }

/-- The room left after adding `v`, if within it. -/
def roomSub (b v : Nat) : Option Nat := if v ≤ b then some (b - v) else none

/-- The window offset after subtracting `v`, if not below the window. -/
def offSub (k v : Nat) : Option Nat := if v ≤ k then some (k - v) else none

/-- A load of `w` bytes at offset `off` from what a register whose window
offset is `k` (if known) holds: public if they are in the window and none of
them is secret. -/
def loadPub (τ : T) (k : Option Nat) (off w : Nat) : Bool :=
  match k with
  | some k => decide (k + off + w ≤ τ.W) && bnone τ.sec (k + off) w
  | none => false

/-- The bytes of the frames open made secret. -/
def framesSec (τ : T) : T := { τ with sec := bset τ.sec τ.sp (τ.W - τ.sp) }

/-- A store of `w` bytes at offset `off` from what a register with window
offset `k` and room `b` (if known) holds, of a value public iff `p`. -/
def storeT (τ : T) (k b : Option Nat) (off w : Nat) (p : Bool) : T :=
  match k with
  | some k =>
    if k + off + w ≤ τ.W then
      { τ with sec := if p then bclr τ.sec (k + off) w else bset τ.sec (k + off) w }
    else if p then τ else framesSec τ
  | none =>
    match b with
    | some b => if off + w ≤ b then τ else if p then τ else framesSec τ
    | none => if p then τ else framesSec τ

/-- An instruction's step, its base register (if it accesses memory) public. -/
def stepB (τ : T) : Instr → Option T
  | .mov d op2 =>
    match op2 with
    | .reg r => some (setR τ d (pubR τ r) (wpOf τ r) (bpOf τ r))
    | _ => some (setR τ d (op2Pub τ op2) none none)
  | .mvn d op2 => some (setR τ d (op2Pub τ op2) none none)
  | .dp op d n op2 =>
    match op, op2 with
    | .add, .imm v =>
      some (setR τ d (pubR τ n) ((wpOf τ n).map (· + v.toNat)) ((bpOf τ n).bind (roomSub · v.toNat)))
    | .sub, .imm v => some (setR τ d (pubR τ n) ((wpOf τ n).bind (offSub · v.toNat)) none)
    | _, _ => some (setR τ d (pubR τ n && op2Pub τ op2) none none)
  | .adds d n op2 | .subs d n op2 =>
    let p := pubR τ n && op2Pub τ op2
    some (setR (setF τ p) d p none none)
  | .adc d n op2 => some (setR τ d (pubR τ n && op2Pub τ op2 && τ.fl) none none)
  | .cmp n op2 => some (setF τ (pubR τ n && op2Pub τ op2))
  | .movw d _ => some (setR τ d true none none)
  | .movt d _ => some (setR τ d (pubR τ d) none none)
  | .adrSym d _ => some (setR τ d false none none)
  | .rev d m => some (setR τ d (pubR τ m) none none)
  | .mul d n m => some (setR τ d (pubR τ n && pubR τ m) none none)
  | .mla d n m a => some (setR τ d (pubR τ n && pubR τ m && pubR τ a) none none)
  | .umaal lo hi n m =>
    let p := pubR τ n && pubR τ m && pubR τ lo && pubR τ hi
    some (setR (setR τ lo p none none) hi p none none)
  | .ldr t n off => some (setR τ t (loadPub τ (wpOf τ n) off 4) none none)
  | .ldrb t n off => some (setR τ t (loadPub τ (wpOf τ n) off 1) none none)
  | .ldrSp t off => some (setR τ t (loadPub τ (some τ.sp) off 4) none none)
  | .str t n off => some (storeT τ (wpOf τ n) (bpOf τ n) off 4 (pubR τ t))
  | .strb t n off => some (storeT τ (wpOf τ n) (bpOf τ n) off 1 (pubR τ t))
  | .addSp d imm => some (setR τ d true (some (τ.sp + imm)) none)
  | .blx _ | .push _ | .pop .. | .alloc _ | .free _ => none

/-- The base register of a load or a store. -/
def base : Instr → Option Reg
  | .ldr _ n _ | .str _ n _ | .ldrb _ n _ | .strb _ n _ => some n
  | _ => none

def step (τ : T) (i : Instr) : Option T :=
  if τ.ok then
    match base i with
    | some n => stepB (withPub τ n) i
    | none => stepB τ i
  else none

/-- A frame of `b` bytes, below the others; or of the registers `rs`
(`push`), whose bytes are public if every one of them is. -/
def push (τ : T) : Instr → Option T
  | .alloc b => if τ.ok && Nat.ble b τ.sp then some { τ with sp := τ.sp - b, nf := τ.nf + 1 } else none
  | .push rs =>
    if τ.ok && Nat.ble (4 * rs.length) τ.sp then
      let n := 4 * rs.length
      let sec := if rs.all (pubR τ) then bclr τ.sec (τ.sp - n) n else bset τ.sec (τ.sp - n) n
      some { τ with sp := τ.sp - n, nf := τ.nf + 1, sec := sec }
    else none
  | _ => none

/-- The innermost frame, of `b` bytes, released; or of `n`, its first word
loaded into `t` (`pop t n`), public if its bytes are. -/
def pop (τ : T) : Instr → Option T
  | .free b =>
    if τ.ok && Nat.blt 0 τ.nf && Nat.ble (τ.sp + b) τ.W then
      some { τ with sp := τ.sp + b, nf := τ.nf - 1 }
    else none
  | .pop t n =>
    if τ.ok && Nat.blt 0 τ.nf && Nat.ble (τ.sp + n) τ.W && Nat.ble (τ.sp + 4) τ.W then
      some { (setR τ t (bnone τ.sec τ.sp 4) none none) with sp := τ.sp + n, nf := τ.nf - 1 }
    else none
  | _ => none

/-- A call: `lr`, `r12` and the flags hold unknowns, public. -/
def call (τ : T) : Option T :=
  if τ.ok then some (setF (setR (setR τ .lr true none none) .r12 true none none) true) else none

def ret (τ : T) : Option T := if τ.ok then some τ else none

/-- Both: what both know, the frames being the same. -/
def meet (τ σ : T) : T :=
  if τ.ok && σ.ok && τ.W == σ.W && τ.sp == σ.sp && τ.nf == σ.nf then
    { τ with
      pub := τ.pub.inter σ.pub
      fl := τ.fl && σ.fl
      wp := τ.wp.filter (fun e => wpOf σ e.1 == some e.2 && wpOf τ e.1 == some e.2)
      bp := τ.bp.filterMap (fun e =>
        if bpOf τ e.1 == some e.2 then (bpOf σ e.1).map (fun b => (e.1, min e.2 b)) else none)
      sec := Nat.lor τ.sec σ.sec }
  else bot

/-- `τ` knows no more than `σ`. -/
def le (τ σ : T) : Bool :=
  !τ.ok ||
    (σ.ok && τ.W == σ.W && τ.sp == σ.sp && τ.nf == σ.nf && τ.pub.subset σ.pub &&
      (!τ.fl || σ.fl) && τ.wp.all (fun e => wpOf σ e.1 == some e.2) &&
      τ.bp.all (fun e => match bpOf σ e.1 with | some b => Nat.ble e.2 b | none => false) &&
      bsub σ.sec τ.sec)

/-- Every register. -/
def allRegs : List Reg :=
  [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

/-- Where the analysis of a function starts, with its window of `W` bytes:
everything public, no frame, and `bp0`, the registers holding the addresses
of buffers (outside the window), with their lengths. -/
def init (W : Nat) (bp0 : List (Reg × Nat)) : T :=
  ⟨true, W, RegSet.ofList allRegs, true, W, 0, [], bp0, 0⟩

/-- Where the analysis of a function must end: every frame released, no byte
of the window secret, `r2`, `r3`, `r12` and the flags public, and of the
result `r1 ++ r0` at most its `rb` low bits secret. -/
def done (rb : Nat) (τ : T) : Bool :=
  τ.ok && τ.nf == 0 && τ.sp == τ.W && τ.sec == 0 && pubR τ .r2 && pubR τ .r3 && pubR τ .r12 && τ.fl &&
    (Nat.ble 64 rb || pubR τ .r1) && (Nat.ble 32 rb || pubR τ .r0)

/-! ## The step the kernel finds again

As on RISC-V64 (see "An analysis the kernel finds again" in the
`proof-performance` skill): `stepK` is `step` (`stepK_eq`) giving a taint
whose fields are evaluated (`forceT`), but the mask of the window's bytes, a
numeral wider than 64 bits, which stays the term it was where the step
leaves it the same number (`forceTS`). `stepK` matches on the instruction
once, with its cases closed (`inline_match%`); `callK`, `pushK`, `popK` and
`meetK` are `call`, `push`, `pop` and `meet`, evaluated likewise. `rtaint`
takes them; the soundness proofs stay about `step` and the others. -/

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

/-- `k τ`, with every field of `τ` evaluated but the mask. -/
def forceT {α : Type} (τ : T) (k : T → α) : α :=
  match τ with
  | ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ =>
    forceBool ok fun ok => forceNat W fun W => pub.force fun pub => forceBool fl fun fl =>
      forceNat sp fun sp => forceNat nf fun nf => forceRegs wp fun wp => forceRegs bp fun bp =>
        k ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩

/-- `forceT`, the mask being the term `sec0` if it is that number. -/
def forceTS {α : Type} (sec0 : Nat) (τ : T) (k : T → α) : α :=
  match τ with
  | ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ =>
    Bool.casesOn (motive := fun _ => α) (Nat.beq sec sec0) (forceT ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ k)
      (forceT ⟨ok, W, pub, fl, sp, nf, wp, bp, sec0⟩ k)

theorem forceTS_eq {α : Type} (sec0 : Nat) (τ : T) (k : T → α) : forceTS sec0 τ k = forceT τ k := by
  obtain ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ := τ
  show Bool.casesOn (motive := fun _ => α) (Nat.beq sec sec0) (forceT ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ k)
    (forceT ⟨ok, W, pub, fl, sp, nf, wp, bp, sec0⟩ k) = _
  cases h : Nat.beq sec sec0
  · rfl
  · rw [Nat.eq_of_beq_eq_true h]

theorem forceT_eq {α : Type} (τ : T) (k : T → α) : forceT τ k = k τ := by
  obtain ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ := τ
  rw [forceT, forceBool_eq, forceNat_eq, RegSet.force_eq, forceBool_eq, forceNat_eq, forceNat_eq,
    forceRegs_eq, forceRegs_eq]

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
  | ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ => forceO sec (stepFnK i ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩)

theorem stepK_eq (τ : T) (i : Instr) : stepK τ i = step τ i := by
  obtain ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ := τ
  rw [stepK, forceO_eq, stepFnK_eq]
  rfl

/-- `call`, giving a taint that is evaluated. -/
def callK (τ : T) : Option T :=
  match τ with
  | ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ => forceO sec (call ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩)

theorem callK_eq (τ : T) : callK τ = call τ := by
  obtain ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ := τ
  exact forceO_eq _ _

/-- `push`, giving a taint that is evaluated. -/
def pushK (τ : T) (i : Instr) : Option T :=
  match τ with
  | ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ => forceO sec (push ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ i)

theorem pushK_eq (τ : T) (i : Instr) : pushK τ i = push τ i := by
  obtain ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ := τ
  exact forceO_eq _ _

/-- `pop`, giving a taint that is evaluated. -/
def popK (τ : T) (i : Instr) : Option T :=
  match τ with
  | ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ => forceO sec (pop ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ i)

theorem popK_eq (τ : T) (i : Instr) : popK τ i = pop τ i := by
  obtain ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ := τ
  exact forceO_eq _ _

/-- `meet`, giving a taint that is evaluated. -/
def meetK (τ σ : T) : T :=
  match τ with
  | ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ => forceTS sec (meet ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ σ) id

theorem meetK_eq (τ σ : T) : meetK τ σ = meet τ σ := by
  obtain ⟨ok, W, pub, fl, sp, nf, wp, bp, sec⟩ := τ
  exact (forceTS_eq _ _ id).trans (forceT_eq _ id)

end VG.Arm.RTaint
