module

public import VerifiedGarbage.Proof.Framework.TaintCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.KernelList
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
step gives where it changes (`maskK`, `forceTS`). `stepK` matches on the
instruction once, with its cases closed (`inline_match%`), and evaluates what
the instruction changes and nothing else (its parts, below); `callK`, `pushK`,
`popK` and `meetK` are `call`, `push`, `pop` and `meet`, with every field of
what they give evaluated. `rtaint`
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

/-! `stepK`'s parts: what an instruction changes is evaluated before the taint
is built of it, and what it does not change is handed on as it was (the lists,
if neither has an entry of the register it writes, `noReg`, `keepL`; the mask,
if the bytes a store writes are in it, or are not, already, `maskK`). -/

open VG.KList (filter find?)

/-- `a == b`, by the registers' indices. -/
def regEq (a b : Reg) : Bool := Nat.beq a.ctorIdx b.ctorIdx

theorem regEq_eq (a b : Reg) : regEq a b = (a == b) := by
  rw [regEq, KList.beq_eq, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => RegIdx.idx_inj h, fun h => h ▸ rfl⟩

/-- The registers of a list's entries. The kernel computes it once for a list,
and for a list with one more entry from that of the list without it. -/
def regsC (l : List (Reg × Nat)) : RegSet Reg := l.foldr (fun e s => s.insert e.1) .empty

@[implemented_by regsC] def regsOf (l : List (Reg × Nat)) : RegSet Reg :=
  List.rec (motive := fun _ => RegSet Reg) .empty (fun e _ ih => ih.insert e.1) l

theorem mem_regsOf {l : List (Reg × Nat)} {r : Reg} : (regsOf l).mem r = l.any fun e => r == e.1 := by
  induction l with
  | nil => exact Bool.eq_false_iff.mpr (RegSet.not_mem_empty r)
  | cons e l ih =>
    rw [List.any_cons, ← ih, Bool.eq_iff_iff, Bool.or_eq_true, beq_iff_eq]
    exact RegSet.mem_insert

/-- The entry of `r` (`wpOf`, `bpOf`). -/
def getK (l : List (Reg × Nat)) (r : Reg) : Option Nat :=
  bif (regsOf l).mem r then (find? (fun e => regEq e.1 r) l).map (·.2) else none

theorem getK_eq (l : List (Reg × Nat)) (r : Reg) : getK l r = (l.find? (·.1 == r)).map (·.2) := by
  simp only [getK, KList.find?_eq, regEq_eq]
  cases h : (regsOf l).mem r
  · rw [mem_regsOf, List.any_eq_false] at h
    rw [Bool.cond_false, List.find?_eq_none.mpr fun e he => by
      have := h e he; rw [Bool.beq_comm]; exact this]
    rfl
  · rfl

theorem filter_of_regsOf {l : List (Reg × Nat)} {d : Reg} (h : (regsOf l).mem d = false) :
    l.filter (·.1 != d) = l := by
  rw [mem_regsOf, List.any_eq_false] at h
  exact List.filter_eq_self.mpr fun e he => by
    rw [bne, Bool.not_eq_true', Bool.beq_comm, Bool.eq_false_iff]; exact h e he

/-- `k` of the entries of `l` but those of `d`, evaluated: `l` as it is, if it has none. -/
def keepL {α : Type} (l : List (Reg × Nat)) (d : Reg) (k : List (Reg × Nat) → α) : α :=
  Bool.casesOn (motive := fun _ => α) ((regsOf l).mem d) (k l) (forceRegs (filter (fun e => !regEq e.1 d) l) k)

theorem keepL_eq {α : Type} (l : List (Reg × Nat)) (d : Reg) (k : List (Reg × Nat) → α) :
    keepL l d k = k (l.filter (·.1 != d)) := by
  simp only [keepL, KList.filter_eq, forceRegs_eq, regEq_eq]
  cases h : (regsOf l).mem d
  · show k l = _
    rw [filter_of_regsOf h]
  · rfl

/-- `k` of the mask after a store of `n` bytes at byte `a`, public if `p`:
`sec` as it is if the store does not change it. -/
def maskK {α : Type} (a n sec : Nat) (p : Bool) (k : Nat → α) : α :=
  Bool.casesOn (motive := fun _ => α) p
    (Bool.casesOn (motive := fun _ => α) (Nat.beq (Nat.land (Nat.shiftRight sec a) (ones n)) (ones n))
      (k (bset sec a n)) (k sec))
    (Bool.casesOn (motive := fun _ => α) (bnone sec a n) (k (bclr sec a n)) (k sec))

/-- What an instruction does to a taint that is `ok`, given the taint's other parts. -/
abbrev Fn := Nat → RegSet Reg → Nat → Nat → Nat → List (Reg × Nat) → List (Reg × Nat) → Nat → Option T

/-- The taint after a secret write of `d`. -/
def setS (d : Reg) : Fn := fun W pub lo sp nf wp bp sec =>
  (pub.erase d).force fun pub =>
    Bool.casesOn (motive := fun _ => Option T) (regEq d .a0) (some ⟨true, W, pub, lo, sp, nf, wp, bp, sec⟩)
      (some ⟨true, W, pub, 64, sp, nf, wp, bp, sec⟩)

/-- The taint after a public write of `d`. -/
def setP (d : Reg) : Fn := fun W pub lo sp nf wp bp sec =>
  (pub.insert d).force fun pub =>
    Bool.casesOn (motive := fun _ => Option T) (regEq d .a0) (some ⟨true, W, pub, lo, sp, nf, wp, bp, sec⟩)
      (some ⟨true, W, pub, 0, sp, nf, wp, bp, sec⟩)

/-- The taint after a write of `d`, public if `p`. -/
def setK (d : Reg) (p : Bool) : Fn := fun W pub lo sp nf wp bp sec =>
  Bool.casesOn (motive := fun _ => Option T) p (setS d W pub lo sp nf wp bp sec) (setP d W pub lo sp nf wp bp sec)

/-- Whether neither list has an entry of `d`. -/
def noReg (wp bp : List (Reg × Nat)) (d : Reg) : Bool :=
  Nat.beq (Nat.land (Nat.lor (regsOf wp).bits (regsOf bp).bits) (RegSet.bit d)) 0

/-- A write of `d` and nothing else, public if `p`. -/
def wr (d : Reg) (p : RegSet Reg → Bool) : Fn := fun W pub lo sp nf wp bp sec =>
  Bool.casesOn (motive := fun _ => Option T) (noReg wp bp d)
    (keepL wp d fun wp => keepL bp d fun bp => setK d (p pub) W pub lo sp nf wp bp sec)
    (setK d (p pub) W pub lo sp nf wp bp sec)

/-- `k` of `l` with the entry `o` of `d` in place of those it has. -/
def ptrL {α : Type} (l : List (Reg × Nat)) (d : Reg) (o : Option Nat) (k : List (Reg × Nat) → α) : α :=
  match o with
  | none => keepL l d k
  | some a => forceNat a fun a => keepL l d fun l => k ((d, a) :: l)

theorem ptrL_eq {α : Type} (l : List (Reg × Nat)) (d : Reg) (o : Option Nat) (k : List (Reg × Nat) → α) :
    ptrL l d o k = k ((match o with | some a => [(d, a)] | none => []) ++ l.filter (·.1 != d)) := by
  cases o <;> simp only [ptrL, forceNat_eq, keepL_eq, List.nil_append, List.cons_append]

/-- `offAdd`, by the cases of `imm`. -/
def offAddK (k : Nat) : Int → Option Nat
  | .ofNat m => some (Nat.add k m)
  | .negSucc m => bif Nat.blt m k then some (Nat.sub k (Nat.succ m)) else none

theorem offAddK_eq (k : Nat) (imm : Int) : offAddK k imm = offAdd k imm := by
  cases imm with
  | ofNat m =>
    rw [offAdd, Int.ofNat_eq_natCast, ite_eq_left (by omega_using [])]; rfl
  | negSucc m =>
    simp only [offAddK, offAdd, Int.negSucc_eq]
    cases h : Nat.blt m k
    · rw [Bool.eq_false_iff, Ne, Nat.blt_eq] at h
      rw [ite_eq_right (by omega_using [h])]; rfl
    · rw [Nat.blt_eq] at h
      rw [ite_eq_left (by omega_using [h])]
      exact congrArg some (show k - (m + 1) = _ by omega_using [h])

/-- `roomAdd`, by the cases of `imm`. -/
def roomAddK (b : Nat) : Int → Option Nat
  | .ofNat m => bif Nat.ble m b then some (Nat.sub b m) else none
  | .negSucc _ => none

theorem roomAddK_eq (b : Nat) (imm : Int) : roomAddK b imm = roomAdd b imm := by
  cases imm with
  | ofNat m =>
    simp only [roomAddK, roomAdd, Int.ofNat_eq_natCast]
    cases h : Nat.ble m b
    · rw [Bool.eq_false_iff, Ne, Nat.ble_eq] at h
      rw [ite_eq_right (by omega_using [h])]; rfl
    · rw [Nat.ble_eq] at h
      rw [ite_eq_left (by omega_using [h])]; rfl
  | negSucc m => rw [roomAdd, ite_eq_right (by rw [Int.negSucc_eq]; omega_using [])]; rfl

/-- `addi`. -/
def addiK (d n : Reg) (imm : Int) : Fn := fun W pub lo sp nf wp bp sec =>
  ptrL wp d ((getK wp n).bind (offAddK · imm)) fun wp =>
    ptrL bp d ((getK bp n).bind (roomAddK · imm)) fun bp =>
      setK d (pub.mem n) W pub lo sp nf wp bp sec

/-- `addSp`. -/
def addSpK (d : Reg) (imm : Nat) : Fn := fun W pub lo sp nf wp bp sec =>
  ptrL wp d (some (Nat.add sp imm)) fun wp => keepL bp d fun bp => setK d true W pub lo sp nf wp bp sec

/-- The low bits of `a0` that may differ after a shift of `a0` itself, secret. -/
def shLo (lo sh : Nat) : ShiftOp → Nat
  | .sll => bif Nat.ble 64 (Nat.add lo sh) then 64 else Nat.add lo sh
  | .srl => Nat.sub lo sh
  | .sra => 64

/-- A shift. -/
def shiftK (op : ShiftOp) (d n : Reg) (sh : Nat) : Size → Fn
  | .w => wr d (·.mem n)
  | .d => fun W pub lo sp nf wp bp sec =>
    bif regEq d .a0 && regEq n .a0 && !pub.mem .a0 then
      keepL wp d fun wp => keepL bp d fun bp => (pub.erase d).force fun pub =>
        forceNat (shLo lo sh op) fun lo => some ⟨true, W, pub, lo, sp, nf, wp, bp, sec⟩
    else wr d (·.mem n) W pub lo sp nf wp bp sec

/-- The low bits of `a0` that may differ once `n` is public (`withPub`). -/
def ldLo (n : Reg) (lo : Nat) : Nat := bif regEq n .a0 then 0 else lo

/-- A load of `w` bytes into `t`, at `off` from `n`. -/
def ldK (w : Nat) (t n : Reg) (off : Nat) : Fn := fun W pub lo sp nf wp bp sec =>
  match getK wp n with
  | none => wr t (fun _ => false) W (pub.insert n) (ldLo n lo) sp nf wp bp sec
  | some k =>
    forceBool (bif Nat.ble (Nat.add (Nat.add k off) w) W then bnone sec (Nat.add k off) w else false) fun p =>
      wr t (fun _ => p) W (pub.insert n) (ldLo n lo) sp nf wp bp sec

/-- `k` of the mask after a store, public if `p`, nowhere known. -/
def stAny {α : Type} (p : Bool) (W sp sec : Nat) (k : Nat → α) : α :=
  bif p then k sec else maskK sp (Nat.sub W sp) sec false k

/-- `k` of the mask after a store of `w` bytes, public if `p`, at `off` from `n`. -/
def stSec {α : Type} (w : Nat) (n : Reg) (off : Nat) (p : Bool) (W sp : Nat) (wp bp : List (Reg × Nat)) (sec : Nat)
    (k : Nat → α) : α :=
  match getK wp n with
  | some b => forceNat (Nat.add b off) fun a => bif Nat.ble (Nat.add a w) W then maskK a w sec p k else stAny p W sp sec k
  | none =>
    bif p then k sec else
      match getK bp n with
      | some b => bif Nat.ble (Nat.add off w) b then k sec else stAny false W sp sec k
      | none => stAny false W sp sec k

/-- A store of `w` bytes of `t`, at `off` from `n`. -/
def stK (w : Nat) (t n : Reg) (off : Nat) : Fn := fun W pub lo sp nf wp bp sec =>
  (pub.insert n).force fun pub => forceNat (ldLo n lo) fun lo =>
    stSec w n off (pub.mem t) W sp wp bp sec fun sec => some ⟨true, W, pub, lo, sp, nf, wp, bp, sec⟩

/-- `step` of a taint that is `ok`, as a function of the instruction first, of
the parts of the taint. -/
def stepFn : Instr → Fn
  | .add d n m | .sub d n m | .addw d n m | .subw d n m | .sltu d n m | .mul d n m
  | .mulhu d n m | .logic _ d n m | .shiftReg _ _ d n m => wr d fun pub => pub.mem n && pub.mem m
  | .addi d n imm => addiK d n imm
  | .addiw d n _ | .logicImm _ d n _ => wr d (·.mem n)
  | .shift op sz d n sh => shiftK op d n sh sz
  | .li d _ | .lui d _ => wr d fun _ => true
  | .addSp d imm => addSpK d imm
  | .load wd t n off => ldK wd.bytes t n off
  | .store wd t n off => stK wd.bytes t n off
  | .lla d _ => wr d fun _ => false
  | .push .. | .pop .. | .alloc .. | .free .. | .jalr .. => fun _ _ _ _ _ _ _ _ => none

/-- `stepFn`, with its cases closed (`inline_match%`). -/
def stepFnK : Instr → Fn := inline_match% VG.RISCV64.RTaint.stepFn

theorem stepFnK_eq (i : Instr) : stepFnK i = stepFn i := by cases i <;> rfl

/-- `step`, giving a taint that is evaluated. -/
def stepK (τ : T) (i : Instr) : Option T :=
  T.casesOn (motive := fun _ => Option T) τ fun ok W pub lo sp nf wp bp sec =>
    Bool.casesOn (motive := fun _ => Option T) ok none (stepFnK i W pub lo sp nf wp bp sec)

theorem ones_eq (w : Nat) : ones w = 2 ^ w - 1 := rfl

theorem bnone_bclr {b d w : Nat} (h : bnone b d w = true) : bclr b d w = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  have h' := Nat.eq_of_beq_eq_true h
  have e : (b &&& (ones w <<< d)).testBit k = false := by
    rw [Nat.testBit_and, Nat.testBit_shiftLeft, ones_eq, Nat.testBit_two_pow_sub_one]
    have hb := congrArg (fun x => x.testBit (k - d)) h'
    simp only [show Nat.land (Nat.shiftRight b d) (ones w) = (b >>> d) &&& (2 ^ w - 1) from rfl, Nat.testBit_and,
      Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Nat.zero_testBit] at hb
    by_cases hk : d ≤ k
    · rw [show d + (k - d) = k by omega] at hb
      simpa [hk] using hb
    · simp [hk]
  show (b ^^^ (b &&& (ones w <<< d))).testBit k = _
  rw [Nat.testBit_xor, e, Bool.xor_false]

theorem ball_bset {b d w : Nat} (h : Nat.beq (Nat.land (Nat.shiftRight b d) (ones w)) (ones w) = true) :
    bset b d w = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  have h' := Nat.eq_of_beq_eq_true h
  show (b ||| (ones w <<< d)).testBit k = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, ones_eq, Nat.testBit_two_pow_sub_one]
  have hb := congrArg (fun x => x.testBit (k - d)) h'
  simp only [show Nat.land (Nat.shiftRight b d) (ones w) = (b >>> d) &&& (2 ^ w - 1) from rfl, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one] at hb
  by_cases hk : d ≤ k
  · rw [show d + (k - d) = k by omega] at hb
    by_cases hw : k - d < w
    · rw [ones_eq, Nat.testBit_two_pow_sub_one, decide_eq_true hw, Bool.and_true] at hb
      rw [hb, Bool.true_or]
    · simp [hw]
  · simp [hk]

theorem maskK_eq {α : Type} (a n sec : Nat) (p : Bool) (k : Nat → α) :
    maskK a n sec p k = k (if p then bclr sec a n else bset sec a n) := by
  cases p <;> simp only [maskK, ↓reduceIte, Bool.false_eq_true]
  · cases h : Nat.beq (Nat.land (Nat.shiftRight sec a) (ones n)) (ones n)
    · rfl
    · rw [ball_bset h]
  · cases h : bnone sec a n
    · rfl
    · rw [bnone_bclr h]

theorem setK_eq (d : Reg) (p : Bool) (W : Nat) (pub : RegSet Reg) (lo sp nf : Nat) (wp bp wp' bp' : List (Reg × Nat))
    (sec : Nat) (k b : Option Nat)
    (hw : wp' = (match k with | some k => [(d, k)] | none => []) ++ wp.filter (·.1 != d))
    (hb : bp' = (match b with | some b => [(d, b)] | none => []) ++ bp.filter (·.1 != d)) :
    setK d p W pub lo sp nf wp' bp' sec = some (setR ⟨true, W, pub, lo, sp, nf, wp, bp, sec⟩ d p k b) := by
  subst hw hb
  cases p
  · simp only [setK, setS, RegSet.force_eq, regEq_eq, setR]
    cases d == Reg.a0 <;> rfl
  · simp only [setK, setP, RegSet.force_eq, regEq_eq, setR]
    cases d == Reg.a0 <;> rfl

theorem noReg_eq {wp bp : List (Reg × Nat)} {d : Reg} (h : noReg wp bp d = true) :
    (regsOf wp).mem d = false ∧ (regsOf bp).mem d = false := by
  have e : ((regsOf wp).bits ||| (regsOf bp).bits) &&& RegSet.bit d = 0 := Nat.eq_of_beq_eq_true h
  have e' := congrArg (fun x => x.testBit (RegIdx.idx d)) e
  simp only [Nat.testBit_and, Nat.testBit_or, RegSet.testBit_bit, decide_true, Bool.and_true, Nat.zero_testBit,
    Bool.or_eq_false_iff] at e'
  exact ⟨Bool.eq_false_iff.mpr fun hm => by rw [← Bool.not_eq_true] at e'; exact e'.1 (RegSet.mem_iff.mp hm),
    Bool.eq_false_iff.mpr fun hm => by
      have h2 := RegSet.mem_iff.mp hm
      rw [e'.2] at h2; cases h2⟩

theorem wr_eq (d : Reg) (p : RegSet Reg → Bool) (W : Nat) (pub : RegSet Reg) (lo sp nf : Nat)
    (wp bp : List (Reg × Nat)) (sec : Nat) :
    wr d p W pub lo sp nf wp bp sec = some (setR ⟨true, W, pub, lo, sp, nf, wp, bp, sec⟩ d (p pub) none none) := by
  have e : ∀ h : Bool, h = noReg wp bp d → Bool.casesOn (motive := fun _ => Option T) h
      (keepL wp d fun wp => keepL bp d fun bp => setK d (p pub) W pub lo sp nf wp bp sec)
      (setK d (p pub) W pub lo sp nf wp bp sec) =
        some (setR ⟨true, W, pub, lo, sp, nf, wp, bp, sec⟩ d (p pub) none none) := by
    intro h hh
    cases h
    · simp only [keepL_eq]
      exact setK_eq d (p pub) W pub lo sp nf wp bp _ _ sec none none rfl rfl
    · obtain ⟨h1, h2⟩ := noReg_eq hh.symm
      exact setK_eq d (p pub) W pub lo sp nf wp bp _ _ sec none none (filter_of_regsOf h1).symm (filter_of_regsOf h2).symm
  exact e _ rfl

theorem withPub_eq (W : Nat) (pub : RegSet Reg) (lo sp nf : Nat) (wp bp : List (Reg × Nat)) (sec : Nat) (n : Reg) :
    withPub ⟨true, W, pub, lo, sp, nf, wp, bp, sec⟩ n =
      ⟨true, W, pub.insert n, ldLo n lo, sp, nf, wp, bp, sec⟩ := by
  rw [withPub, ldLo, regEq_eq]
  cases n == Reg.a0 <;> rfl

theorem shiftK_eq (op : ShiftOp) (sz : Size) (d n : Reg) (sh : Nat) (W : Nat) (pub : RegSet Reg) (lo sp nf : Nat)
    (wp bp : List (Reg × Nat)) (sec : Nat) :
    shiftK op d n sh sz W pub lo sp nf wp bp sec =
      stepB ⟨true, W, pub, lo, sp, nf, wp, bp, sec⟩ (.shift op sz d n sh) := by
  cases sz with
  | w =>
    simp only [shiftK, wr_eq, stepB, show (Size.w == Size.d) = false from rfl, Bool.and_false, Bool.false_and]
    rfl
  | d =>
    simp only [shiftK, wr_eq, stepB, regEq_eq, show (Size.d == Size.d) = true from rfl, Bool.and_true, pubR]
    cases h : d == Reg.a0 && n == Reg.a0 && !pub.mem Reg.a0
    · rfl
    · simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
      obtain ⟨⟨rfl, rfl⟩, hp⟩ := h
      simp only [keepL_eq, RegSet.force_eq, forceNat_eq, setR, hp, Bool.cond_true, ↓reduceIte]
      cases op with
      | sll =>
        simp only [shLo, KList.ble_eq, show Nat.add lo sh = lo + sh from rfl]
        by_cases hl : 64 ≤ lo + sh
        · rw [decide_eq_true hl, Nat.min_eq_left hl]; rfl
        · rw [decide_eq_false hl, Nat.min_eq_right (by omega)]; rfl
      | srl => rfl
      | sra => rfl

theorem stAny_eq {α : Type} (p : Bool) (W sp sec : Nat) (k : Nat → α) :
    stAny p W sp sec k = k (if p then sec else bset sec sp (W - sp)) := by
  cases p
  · exact maskK_eq sp (W - sp) sec false k
  · rfl

theorem stepFn_eq (i : Instr) (W : Nat) (pub : RegSet Reg) (lo sp nf : Nat) (wp bp : List (Reg × Nat)) (sec : Nat) :
    stepFn i W pub lo sp nf wp bp sec = step ⟨true, W, pub, lo, sp, nf, wp, bp, sec⟩ i := by
  cases i with
  | addi d n imm =>
    simp only [stepFn, addiK, ptrL_eq, getK_eq, show (offAddK · imm) = (offAdd · imm) from funext fun _ => offAddK_eq _ _,
      show (roomAddK · imm) = (roomAdd · imm) from funext fun _ => roomAddK_eq _ _]
    exact setK_eq d _ W pub lo sp nf wp bp _ _ sec _ _ rfl rfl
  | addSp d imm =>
    simp only [stepFn, addSpK, ptrL_eq, keepL_eq]
    exact setK_eq d _ W pub lo sp nf wp bp _ _ sec _ none rfl rfl
  | shift op sz d n sh => exact shiftK_eq op sz d n sh W pub lo sp nf wp bp sec
  | load wd t n off =>
    show ldK wd.bytes t n off W pub lo sp nf wp bp sec =
      stepB (withPub ⟨true, W, pub, lo, sp, nf, wp, bp, sec⟩ n) (.load wd t n off)
    rw [withPub_eq]
    simp only [ldK, getK_eq, stepB, wpOf, wr_eq, forceBool_eq, KList.ble_eq,
      show ∀ a b : Nat, Nat.add a b = a + b from fun _ _ => rfl]
    cases (wp.find? (·.1 == n)).map (·.2) with
    | none => rfl
    | some k =>
      simp only
      cases decide (k + off + wd.bytes ≤ W) <;> rfl
  | store wd t n off =>
    show stK wd.bytes t n off W pub lo sp nf wp bp sec =
      stepB (withPub ⟨true, W, pub, lo, sp, nf, wp, bp, sec⟩ n) (.store wd t n off)
    rw [withPub_eq]
    simp only [stK, stSec, getK_eq, stepB, wpOf, bpOf, forceNat_eq, RegSet.force_eq, KList.ble_eq, maskK_eq, stAny_eq,
      show ∀ a b : Nat, Nat.add a b = a + b from fun _ _ => rfl]
    rw [show (pub.insert n).mem t = pubR ⟨true, W, pub.insert n, ldLo n lo, sp, nf, wp, bp, sec⟩ t from rfl]
    generalize pubR ⟨true, W, pub.insert n, ldLo n lo, sp, nf, wp, bp, sec⟩ t = p
    cases (wp.find? (·.1 == n)).map (·.2) with
    | some k =>
      by_cases h : k + off + wd.bytes ≤ W
      · simp only [h, decide_true, Bool.cond_true, ↓reduceIte]
      · simp only [h, decide_false, Bool.cond_false, ↓reduceIte]
        cases p <;> rfl
    | none =>
      cases (bp.find? (·.1 == n)).map (·.2) with
      | none => cases p <;> rfl
      | some b =>
        by_cases h : off + wd.bytes ≤ b
        · simp only [h, decide_true, Bool.cond_true, ↓reduceIte]
          cases p <;> rfl
        · simp only [h, decide_false, Bool.cond_false, ↓reduceIte]
          cases p <;> rfl
  | push | pop | alloc | free | jalr => rfl
  | add d n m | sub d n m | addw d n m | subw d n m | sltu d n m | mul d n m | mulhu d n m | logic _ d n m
  | shiftReg _ _ d n m => exact wr_eq d (fun pub => pub.mem n && pub.mem m) W pub lo sp nf wp bp sec
  | addiw d n | logicImm _ d n => exact wr_eq d (·.mem n) W pub lo sp nf wp bp sec
  | li d | lui d => exact wr_eq d (fun _ => true) W pub lo sp nf wp bp sec
  | lla d => exact wr_eq d (fun _ => false) W pub lo sp nf wp bp sec

theorem stepK_eq (τ : T) (i : Instr) : stepK τ i = step τ i := by
  obtain ⟨ok, W, pub, lo, sp, nf, wp, bp, sec⟩ := τ
  cases ok
  · rfl
  · show stepFnK i W pub lo sp nf wp bp sec = _
    rw [stepFnK_eq, stepFn_eq]

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
