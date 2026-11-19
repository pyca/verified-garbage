module

public import VerifiedGarbage.Proof.Framework.TaintCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.TaintCT
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Omega

/-!
# What a function leaves in its registers and on its stack (64-bit RISC-V)

`rtaint W` is a taint analysis for two runs that leak the same (`TaintCT`) of
code whose stack is the `W` bytes below the stack pointer on entry (its
*window*). It follows the frames the code allocates (`alloc`, `free`, and
`push`, `pop` of a register, whose frame holds it), which
are nested in the window from its top down, and keeps, as a bit mask, the
bytes of the window that may differ between the two runs (`sec`). What it
knows of a register:

* whether it holds the same value in both runs (`pub`), and how many low
  bits of `a0`, the result, may differ (`lo`);
* whether it holds the address of byte `k` of the window (`wp`): a store
  through it then writes bytes the analysis knows, and a load through it reads
  them, public if they are;
* whether the `room` bytes from the address it holds are outside the window
  (`bp`), as those of a buffer are: a store through it within them leaves the
  window as it was.

The model faults on a store that is not within one writable region (`wr`),
which are the frames and the buffers: a store the analysis cannot place is in
a frame still allocated, or in a buffer, so a secret stored there makes only
the bytes of the frames secret (`sec` from the stack pointer up). The bytes of
a frame the code releases are what it left there, or what replaces them
(`lose`), which the two runs' unknowns, shared, decide alike. A call leaves
the unknowns in `ra` and `t0`–`t6`, the same in both runs: they are public.

`ResidueTaintSound.lean` proves it sound.
-/

@[expose] public section

namespace VG.RISCV64.RTaint

open VG.RISCV64

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
  lo : Nat
  sp : Nat
  nf : Nat
  wp : List (Reg × Nat)
  bp : List (Reg × Nat)
  sec : Nat
  deriving Lean.ToExpr

/-- What knows nothing. -/
def bot : T := ⟨false, 0, RegSet.empty, 64, 0, 0, [], [], 0⟩

/-- The offset into the window `r` holds, if known. -/
def wpOf (τ : T) (r : Reg) : Option Nat := (τ.wp.find? (·.1 == r)).map (·.2)

/-- The bytes outside the window from the address `r` holds, if known. -/
def bpOf (τ : T) (r : Reg) : Option Nat := (τ.bp.find? (·.1 == r)).map (·.2)

def pubR (τ : T) (r : Reg) : Bool := τ.pub.mem r

/-- `τ` with `d` written: public iff `p`, the window offset `k` and the room
`b` if known. -/
def setR (τ : T) (d : Reg) (p : Bool) (k b : Option Nat) : T :=
  { τ with
    pub := if p then τ.pub.insert d else τ.pub.erase d
    lo := if d == .a0 then (if p then 0 else 64) else τ.lo
    wp := (match k with | some k => [(d, k)] | none => []) ++ τ.wp.filter (·.1 != d)
    bp := (match b with | some b => [(d, b)] | none => []) ++ τ.bp.filter (·.1 != d) }

/-- `τ` with `n` public (the base register of an access, whose address is
the same in both runs). -/
def withPub (τ : T) (n : Reg) : T :=
  if n == .a0 then { τ with pub := τ.pub.insert n, lo := 0 } else { τ with pub := τ.pub.insert n }

/-- Byte `k` of the window plus `imm`, if not below it. -/
def offAdd (k : Nat) (imm : Int) : Option Nat :=
  if 0 ≤ (k : Int) + imm then some ((k : Int) + imm).toNat else none

/-- The room left after adding `imm`, if within it. -/
def roomAdd (b : Nat) (imm : Int) : Option Nat :=
  if 0 ≤ imm ∧ imm ≤ (b : Int) then some (b - imm.toNat) else none

/-- An instruction's step, its base register (if it accesses memory) public. -/
def stepB (τ : T) : Instr → Option T
  | .add d n m | .sub d n m | .addw d n m | .subw d n m | .sltu d n m | .mul d n m
  | .mulhu d n m | .logic _ d n m | .shiftReg _ _ d n m =>
    some (setR τ d (pubR τ n && pubR τ m) none none)
  | .addi d n imm =>
    some (setR τ d (pubR τ n) ((wpOf τ n).bind (offAdd · imm)) ((bpOf τ n).bind (roomAdd · imm)))
  | .addiw d n _ | .logicImm _ d n _ => some (setR τ d (pubR τ n) none none)
  | .shift op sz d n sh =>
    let τ' := setR τ d (pubR τ n) none none
    -- The low bits of `a0` that may differ, through a shift of `a0` itself.
    if d == .a0 && n == .a0 && sz == Size.d && !pubR τ .a0 then
      match op with
      | .sll => some { τ' with lo := min 64 (τ.lo + sh) }
      | .srl => some { τ' with lo := τ.lo - sh }
      | .sra => some τ'
    else some τ'
  | .li d _ | .lui d _ => some (setR τ d true none none)
  | .addSp d imm => some (setR τ d true (some (τ.sp + imm)) none)
  | .load wd t n off =>
    let p := match wpOf τ n with
      | some k => decide (k + off + wd.bytes ≤ τ.W) && bnone τ.sec (k + off) wd.bytes
      | none => false
    some (setR τ t p none none)
  | .store wd t n off =>
    match wpOf τ n with
    | some k =>
      if k + off + wd.bytes ≤ τ.W then
        let sec := if pubR τ t then bclr τ.sec (k + off) wd.bytes else bset τ.sec (k + off) wd.bytes
        some { τ with sec := sec }
      else if pubR τ t then some τ else some { τ with sec := bset τ.sec τ.sp (τ.W - τ.sp) }
    | none =>
      match bpOf τ n with
      | some b =>
        if off + wd.bytes ≤ b then some τ
        else if pubR τ t then some τ else some { τ with sec := bset τ.sec τ.sp (τ.W - τ.sp) }
      | none => if pubR τ t then some τ else some { τ with sec := bset τ.sec τ.sp (τ.W - τ.sp) }
  | .lla d _ => some (setR τ d false none none)
  | .push .. | .pop .. | .alloc .. | .free .. | .jalr .. => none

/-- The base register of a load or a store. -/
def base : Instr → Option Reg
  | .load _ _ n _ | .store _ _ n _ => some n
  | _ => none

def step (τ : T) (i : Instr) : Option T :=
  if τ.ok then
    match base i with
    | some n => stepB (withPub τ n) i
    | none => stepB τ i
  else none

/-- A frame of `b` bytes, below the others; or of 16, holding `r` in its high
doubleword (`push r`). -/
def push (τ : T) : Instr → Option T
  | .alloc b => if τ.ok && Nat.ble b τ.sp then some { τ with sp := τ.sp - b, nf := τ.nf + 1 } else none
  | .push r =>
    if τ.ok && Nat.ble 16 τ.sp then
      let sec := if pubR τ r then bclr τ.sec (τ.sp - 16 + 8) 8 else bset τ.sec (τ.sp - 16 + 8) 8
      some { τ with sp := τ.sp - 16, nf := τ.nf + 1, sec := sec }
    else none
  | _ => none

/-- The innermost frame, of `b` bytes, released; or of 16, its high
doubleword loaded into `r` (`pop r`), public if its bytes are. -/
def pop (τ : T) : Instr → Option T
  | .free b =>
    if τ.ok && Nat.blt 0 τ.nf && Nat.ble (τ.sp + b) τ.W then
      some { τ with sp := τ.sp + b, nf := τ.nf - 1 }
    else none
  | .pop r =>
    if τ.ok && Nat.blt 0 τ.nf && Nat.ble (τ.sp + 16) τ.W then
      some { (setR τ r (bnone τ.sec (τ.sp + 8) 8) none none) with sp := τ.sp + 16, nf := τ.nf - 1 }
    else none
  | _ => none

/-- The registers a call writes, with the unknowns: public. -/
def callRegs : List Reg := [.ra, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

def call (τ : T) : Option T :=
  if τ.ok then some (callRegs.foldl (fun τ r => setR τ r true none none) τ) else none

def ret (τ : T) : Option T := if τ.ok then some τ else none

/-- Both: what both know, the frames being the same. -/
def meet (τ σ : T) : T :=
  if τ.ok && σ.ok && τ.W == σ.W && τ.sp == σ.sp && τ.nf == σ.nf then
    { τ with
      pub := τ.pub.inter σ.pub
      lo := max τ.lo σ.lo
      wp := τ.wp.filter (fun e => wpOf σ e.1 == some e.2 && wpOf τ e.1 == some e.2)
      bp := τ.bp.filterMap (fun e =>
        if bpOf τ e.1 == some e.2 then (bpOf σ e.1).map (fun b => (e.1, min e.2 b)) else none)
      sec := Nat.lor τ.sec σ.sec }
  else bot

/-- `τ` knows no more than `σ`. -/
def le (τ σ : T) : Bool :=
  !τ.ok ||
    (σ.ok && τ.W == σ.W && τ.sp == σ.sp && τ.nf == σ.nf && τ.pub.subset σ.pub &&
      Nat.ble σ.lo τ.lo && τ.wp.all (fun e => wpOf σ e.1 == some e.2) &&
      τ.bp.all (fun e => match bpOf σ e.1 with | some b => Nat.ble e.2 b | none => false) &&
      bsub σ.sec τ.sec)

/-- Where the analysis of a function starts, with its window of `W` bytes:
everything public, no frame, and `bp0`, the registers holding the addresses
of buffers (outside the window), with their lengths. -/
def init (W : Nat) (bp0 : List (Reg × Nat)) : T :=
  ⟨true, W, RegSet.ofList allRegs, 0, W, 0, [], bp0, 0⟩
where
  allRegs : List Reg := [.ra, .t0, .t1, .t2, .s0, .s1, .a0, .a1, .a2, .a3, .a4,
    .a5, .a6, .a7, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11, .t3, .t4, .t5, .t6]

/-- The registers the calling convention does not preserve, but `a0`. -/
def scratch : List Reg :=
  [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

/-- Where the analysis of a function must end: every frame released, no byte
of the window secret, every register the calling convention does not
preserve public, and at most the `r` low bits of `a0` secret. -/
def done (r : Nat) (τ : T) : Bool :=
  τ.ok && τ.nf == 0 && τ.sp == τ.W && τ.sec == 0 && scratch.all (pubR τ) && Nat.ble τ.lo r

/-! ## The step the kernel finds again

`step` gives a taint whose fields are terms in the taint before
(`{ τ with pub := … }`): no two taints of a check are the same term, a field is
read through every taint since it last changed, and the kernel, which
remembers the value of every term it has evaluated, by the term, evaluates
every instruction of the code. `stepK` is `step` (`stepK_eq`) giving a taint
whose fields are evaluated (`forceT`), but the mask of the window's bytes: a
numeral wider than 64 bits, of which the kernel's hash is of the low 64, so
that taints that differ only above them would have one hash. The mask stays
the term it was where the step leaves it the same number, and is the term the
step gives where it changes (`forceTS`). `stepK` matches on the instruction
once, with its cases closed (`inline_match%`); `callK`, `pushK`, `popK` and
`meetK` are `call`, `push`, `pop` and `meet`, evaluated likewise. `rtaint`
takes them; the soundness proofs stay about `step` and the others. See "An
analysis the kernel finds again" in the `proof-performance` skill. -/

/-- `k n`, with the number `n` evaluated (as `RegSet.force` evaluates a set). -/
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
  | ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ =>
    forceBool ok fun ok => forceNat W fun W => pub.force fun pub => forceNat lo fun lo =>
      forceNat sp fun sp => forceNat nf fun nf => forceRegs wp fun wp => forceRegs bp fun bp =>
        k ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩

/-- `forceT`, the mask being the term `sec0` if it is that number. -/
def forceTS {α : Type} (sec0 : Nat) (τ : T) (k : T → α) : α :=
  match τ with
  | ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ =>
    Bool.casesOn (motive := fun _ => α) (Nat.beq sec sec0) (forceT ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ k)
      (forceT ⟨ok, W, pub, lo, sp, nf, wp, bp, sec0⟩ k)

theorem forceTS_eq {α : Type} (sec0 : Nat) (τ : T) (k : T → α) : forceTS sec0 τ k = forceT τ k := by
  obtain ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ := τ
  show Bool.casesOn (motive := fun _ => α) (Nat.beq sec sec0) (forceT ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ k)
    (forceT ⟨ok, W, pub, lo, sp, nf, wp, bp, sec0⟩ k) = _
  cases h : Nat.beq sec sec0
  · rfl
  · rw [Nat.eq_of_beq_eq_true h]

theorem forceT_eq {α : Type} (τ : T) (k : T → α) : forceT τ k = k τ := by
  obtain ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ := τ
  rw [forceT, forceBool_eq, forceNat_eq, RegSet.force_eq, forceNat_eq, forceNat_eq, forceNat_eq,
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
  | ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ => forceO sec (stepFnK i ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩)

theorem stepK_eq (τ : T) (i : Instr) : stepK τ i = step τ i := by
  obtain ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ := τ
  rw [stepK, forceO_eq, stepFnK_eq]
  rfl

/-- `call`, giving a taint that is evaluated. -/
def callK (τ : T) : Option T :=
  match τ with
  | ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ => forceO sec (call ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩)

theorem callK_eq (τ : T) : callK τ = call τ := by
  obtain ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ := τ
  exact forceO_eq _ _

/-- `push`, giving a taint that is evaluated. -/
def pushK (τ : T) (i : Instr) : Option T :=
  match τ with
  | ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ => forceO sec (push ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ i)

theorem pushK_eq (τ : T) (i : Instr) : pushK τ i = push τ i := by
  obtain ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ := τ
  exact forceO_eq _ _

/-- `pop`, giving a taint that is evaluated. -/
def popK (τ : T) (i : Instr) : Option T :=
  match τ with
  | ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ => forceO sec (pop ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ i)

theorem popK_eq (τ : T) (i : Instr) : popK τ i = pop τ i := by
  obtain ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ := τ
  exact forceO_eq _ _

/-- `meet`, giving a taint that is evaluated. -/
def meetK (τ σ : T) : T :=
  match τ with
  | ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ => forceTS sec (meet ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ σ) id

theorem meetK_eq (τ σ : T) : meetK τ σ = meet τ σ := by
  obtain ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ := τ
  exact (forceTS_eq _ _ id).trans (forceT_eq _ id)

end VG.RISCV64.RTaint
