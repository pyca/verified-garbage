module

public import VerifiedGarbage.Proof.Framework.TaintCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.Writes
public import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
public meta import VerifiedGarbage.Proof.Framework.TaintCT
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.Writes
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-!
# What a function leaves in its registers and on its stack (64-bit little-endian PowerPC)

`rtaint` (`ResidueTaintSound.lean`) is a taint analysis for two runs that leak
the same (`TaintCT`) of code whose stack is the `W` bytes below the stack
pointer on entry (its *window*), as on RISC-V (`Proof/Framework/RISCV64/ResidueTaint.lean`).
It follows the frames the code pushes (`push`, `alloc`, then `pop`, `free`),
which are nested in the window from its top down, and keeps, as a bit mask,
the bytes of the window that may differ between the two runs (`sec`). What
it knows of a register:

* whether a general-purpose register holds the same value in both runs
  (`pub`), how many low bits of `r3`, the result, may differ (`lo`), and
  likewise of the vector registers (`vpub`), CA (`ca`) and the link register
  (`lr`);
* whether it holds the address of byte `k` of the window (`wp`): a store
  through it then writes bytes the analysis knows, and a load through it reads
  them, public if they are;
* whether the `room` bytes from the address it holds are outside the window
  (`bp`), as those of a buffer are: a store through it within them leaves the
  window as it was.

A frame of `b` bytes pushed at offset `o` of the window has its region at
`o + 32`, past the 32-byte header (`TCB/PPC64LE/Isa.lean`, `push`), whose
first doubleword the push stores: the back chain, the old stack pointer, the
same in both runs. The model faults on a store that is not within one
writable region, the frames' and the buffers': a store the analysis cannot
place (through a register it does not know, or `RA + RB`) is in a frame
still allocated or in a buffer, so a secret stored there makes the bytes of
the frames secret (`sec` from the stack pointer up), and a public one, at the
address both runs access, the same bytes in both. The bytes of a frame the
code releases are what it left there, or what replaces them (`lose`), which
the two runs' unknowns, shared, decide alike. A call leaves unknowns in
`LR`, `r0`, `r11` and `r12`, the same in both runs: they are public.
`mtvsrd`'s undefined half is a function, shared, of its operands and an
unknown: public if they are.
-/

@[expose] public section

namespace VG.PPC64LE

instance : RegIdx VReg := ⟨VReg.ctorIdx, fun {a b} h => by rw [← VReg.ofNat_ctorIdx a, h, VReg.ofNat_ctorIdx]⟩

/-- The vector registers an instruction reads. -/
def VOp.srcs : VOp → List VReg
  | .cipher _ _ _ n m | .pmsumd _ n m | .logic _ _ n m | .add _ _ n m | .sldoi _ n m _ | .rlw _ n m
  | .addh _ n m | .sub _ _ n m | .minu _ _ n m | .mulu _ _ _ n m | .muluwm _ n m | .shifth _ _ n m => [n, m]
  | .sbox _ n | .sha256 _ n .. | .sha512 _ n .. | .splat _ _ n _ => [n]
  | .sel _ n m c | .perm _ n m c | .mladduhm _ n m c => [n, m, c]
  | .splatImm .. => []

end VG.PPC64LE

namespace VG.PPC64LE.RTaint

open VG.PPC64LE

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
  vpub : RegSet VReg
  ca : Bool
  lr : Bool
  sp : Nat
  nf : Nat
  wp : List (Reg × Nat)
  bp : List (Reg × Nat)
  sec : Nat
  deriving Lean.ToExpr

/-- What knows nothing. -/
def bot : T := ⟨false, 0, RegSet.empty, 64, RegSet.empty, false, false, 0, 0, [], [], 0⟩

/-- The offset into the window `r` holds, if known. -/
def wpOf (τ : T) (r : Reg) : Option Nat := (τ.wp.find? (·.1 == r)).map (·.2)

/-- The bytes outside the window from the address `r` holds, if known. -/
def bpOf (τ : T) (r : Reg) : Option Nat := (τ.bp.find? (·.1 == r)).map (·.2)

def pubR (τ : T) (r : Reg) : Bool := τ.pub.mem r

def pubV (τ : T) (v : VReg) : Bool := τ.vpub.mem v

/-- `τ` with `d` written: public iff `p`, the window offset `k` and the room
`b` if known. -/
def setR (τ : T) (d : Reg) (p : Bool) (k b : Option Nat) : T :=
  { τ with
    pub := if p then τ.pub.insert d else τ.pub.erase d
    lo := if d == .r3 then (if p then 0 else 64) else τ.lo
    wp := (match k with | some k => [(d, k)] | none => []) ++ τ.wp.filter (·.1 != d)
    bp := (match b with | some b => [(d, b)] | none => []) ++ τ.bp.filter (·.1 != d) }

/-- `τ` with the vector register `d` written: public iff `p`. -/
def setV (τ : T) (d : VReg) (p : Bool) : T :=
  { τ with vpub := if p then τ.vpub.insert d else τ.vpub.erase d }

/-- `τ` with `n` public (the base register of an access, whose address is
the same in both runs). -/
def withPub (τ : T) (n : Reg) : T :=
  if n == .r3 then { τ with pub := τ.pub.insert n, lo := 0 } else { τ with pub := τ.pub.insert n }

/-- The room left after adding `imm`, if within it. -/
def roomAdd (b imm : Nat) : Option Nat := if imm ≤ b then some (b - imm) else none

/-- The frames' bytes made secret: a store the analysis cannot place. -/
def secFrames (τ : T) : T := { τ with sec := bset τ.sec τ.sp (τ.W - τ.sp) }

/-- A store of `n` bytes, public iff `p`, through a register at byte `k` of
the window plus `off`, if known (`wk`), or with `b` bytes of room outside it
(`bk`). -/
def storeAt (τ : T) (p : Bool) (wk bk : Option Nat) (off n : Nat) : T :=
  match wk with
  | some k =>
    if k + off + n ≤ τ.W then
      { τ with sec := if p then bclr τ.sec (k + off) n else bset τ.sec (k + off) n }
    else if p then τ else secFrames τ
  | none =>
    match bk with
    | some b => if off + n ≤ b then τ else if p then τ else secFrames τ
    | none => if p then τ else secFrames τ

/-- Whether the `n` bytes at byte `k` of the window plus `off` (`wk`) are
public. -/
def loadPub (τ : T) (wk : Option Nat) (off n : Nat) : Bool :=
  match wk with
  | some k => decide (k + off + n ≤ τ.W) && bnone τ.sec (k + off) n
  | none => false

/-- What a shift of `r3` into itself leaves of `lo`. -/
def shiftLo (τ τ' : T) (d n : Reg) (left : Bool) (sh : Nat) : T :=
  if d == .r3 && n == .r3 && !pubR τ .r3 then
    { τ' with lo := if left then min 64 (τ.lo + sh) else τ.lo - sh }
  else τ'

/-- An instruction's step, its base register (if it accesses memory) public. -/
def stepB (τ : T) : Instr → Option T
  | .add d n m | .sub d n m | .mul d n m | .mulhu d n m | .logic _ d n m =>
    some (setR τ d (pubR τ n && pubR τ m) none none)
  | .addc d n m | .subc d n m =>
    some { setR τ d (pubR τ n && pubR τ m) none none with ca := pubR τ n && pubR τ m }
  | .adde d n m | .sube d n m =>
    let p := pubR τ n && pubR τ m && τ.ca
    some { setR τ d p none none with ca := p }
  | .addze d n =>
    let p := pubR τ n && τ.ca
    some { setR τ d p none none with ca := p }
  | .addi d n imm =>
    some (setR τ d (pubR τ n) ((wpOf τ n).map (· + imm)) ((bpOf τ n).bind (roomAdd · imm)))
  | .subi d n imm =>
    some (setR τ d (pubR τ n) ((wpOf τ n).bind fun k => if imm ≤ k then some (k - imm) else none) none)
  | .li d _ | .lis d _ => some (setR τ d true none none)
  | .ori d n _ | .oris d n _ | .rotr _ d n _ => some (setR τ d (pubR τ n) none none)
  | .lsr sz d n sh =>
    let τ' := setR τ d (pubR τ n) none none
    if sz == Size.d then some (shiftLo τ τ' d n false sh) else some τ'
  | .lsl d n sh => some (shiftLo τ (setR τ d (pubR τ n) none none) d n true sh)
  | .addSp d imm => some (setR τ d true (some (τ.sp + imm)) none)
  | .load sz t n off => some (setR τ t (loadPub τ (wpOf τ n) off sz.bytes) none none)
  | .lbz t n off => some (setR τ t (loadPub τ (wpOf τ n) off 1) none none)
  | .store sz t n off => some (storeAt τ (pubR τ t) (wpOf τ n) (bpOf τ n) off sz.bytes)
  | .stb t n off => some (storeAt τ (pubR τ t) (wpOf τ n) (bpOf τ n) off 1)
  | .loadRev _ t _ _ => some (setR τ t false none none)
  | .storeRev sz t _ _ => some (storeAt τ (pubR τ t) none none 0 sz.bytes)
  | .mflr d => some (setR τ d τ.lr none none)
  | .mtlr r => some { τ with lr := pubR τ r }
  | .adrSym d _ => some { setR τ d false none none with lr := true }
  | .vop op => some (setV τ op.dst (op.srcs.all (pubV τ)))
  | .lxvd2x d _ _ => some (setV τ d false)
  | .lxvd2xTbl d _ b _ _ => some (setV τ d (pubR τ b))
  | .stxvd2x n _ _ => some (storeAt τ (pubV τ n) none none 0 16)
  | .mtvsrd d n => some (setV τ d (pubR τ n && pubV τ d))
  | .mfvsrd d n => some (setR τ d (pubV τ n) none none)
  | .push .. | .pop .. | .alloc .. | .free .. | .bctrl => none

/-- The base register of a D-form load or store. -/
def base : Instr → Option Reg
  | .load _ _ n _ | .store _ _ n _ | .lbz _ n _ | .stb _ n _ => some n
  | _ => none

def step (τ : T) (i : Instr) : Option T :=
  if τ.ok then
    match base i with
    | some n => stepB (withPub τ n) i
    | none => stepB τ i
  else none

/-- A frame below the others: `push r`'s of 48 bytes, holding `r` at its
byte 32, or `alloc b`'s. Each stores the back chain, the old stack pointer,
at its byte 0. -/
def push (τ : T) : Instr → Option T
  | .push r =>
    if τ.ok && Nat.ble 48 τ.sp then
      let o := τ.sp - 48
      some { τ with
        sp := o, nf := τ.nf + 1
        sec := let s := bclr τ.sec o 8; if pubR τ r then bclr s (o + 32) 8 else bset s (o + 32) 8 }
    else none
  | .alloc b =>
    if τ.ok && Nat.blt 32 b && Nat.ble b τ.sp then
      some { τ with sp := τ.sp - b, nf := τ.nf + 1, sec := bclr τ.sec (τ.sp - b) 8 }
    else none
  | _ => none

/-- The innermost frame released: `pop r`'s, which loads `r` from its byte
32, or `free b`'s. -/
def pop (τ : T) : Instr → Option T
  | .pop r =>
    if τ.ok && Nat.blt 0 τ.nf && Nat.ble (τ.sp + 48) τ.W then
      some { setR τ r (bnone τ.sec (τ.sp + 32) 8) none none with sp := τ.sp + 48, nf := τ.nf - 1 }
    else none
  | .free b =>
    if τ.ok && Nat.blt 0 τ.nf && Nat.ble (τ.sp + b) τ.W then
      some { τ with sp := τ.sp + b, nf := τ.nf - 1 }
    else none
  | _ => none

/-- The registers a call writes with the unknowns, besides `LR`: public. -/
def callRegs : List Reg := [.r0, .r11, .r12]

def call (τ : T) : Option T :=
  if τ.ok then some { callRegs.foldl (fun τ r => setR τ r true none none) τ with lr := true } else none

def ret (τ : T) : Option T := if τ.ok then some τ else none

/-- Both: what both know, the frames being the same. -/
def meet (τ σ : T) : T :=
  if τ.ok && σ.ok && τ.W == σ.W && τ.sp == σ.sp && τ.nf == σ.nf then
    { τ with
      pub := τ.pub.inter σ.pub
      lo := max τ.lo σ.lo
      vpub := τ.vpub.inter σ.vpub
      ca := τ.ca && σ.ca
      lr := τ.lr && σ.lr
      wp := τ.wp.filter (fun e => wpOf σ e.1 == some e.2 && wpOf τ e.1 == some e.2)
      bp := τ.bp.filterMap (fun e =>
        if bpOf τ e.1 == some e.2 then (bpOf σ e.1).map (fun b => (e.1, min e.2 b)) else none)
      sec := Nat.lor τ.sec σ.sec }
  else bot

/-- `τ` knows no more than `σ`. -/
def le (τ σ : T) : Bool :=
  !τ.ok ||
    (σ.ok && τ.W == σ.W && τ.sp == σ.sp && τ.nf == σ.nf && τ.pub.subset σ.pub &&
      Nat.ble σ.lo τ.lo && τ.vpub.subset σ.vpub && (!τ.ca || σ.ca) && (!τ.lr || σ.lr) &&
      τ.wp.all (fun e => wpOf σ e.1 == some e.2) &&
      τ.bp.all (fun e => match bpOf σ e.1 with | some b => Nat.ble e.2 b | none => false) &&
      bsub σ.sec τ.sec)

/-- Every general-purpose register. -/
def allRegs : List Reg := [.r0, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12,
  .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28,
  .r29, .r30, .r31]

/-- Where the analysis of a function starts, with its window of `W` bytes:
everything public, no frame, and `bp0`, the registers holding the addresses
of buffers (outside the window), with their lengths. -/
def init (W : Nat) (bp0 : List (Reg × Nat)) : T :=
  ⟨true, W, RegSet.ofList allRegs, 0, RegSet.ofList Impl.Scrub.PPC64LE.vregs, true, true, W, 0, [], bp0, 0⟩

/-- The volatile registers but `r3`. -/
def scratch : List Reg := .r0 :: Impl.Scrub.PPC64LE.scratchRegs

/-- Where the analysis of a function must end: every frame released, no byte
of the window secret, every volatile register but `r3`, every vector
register and CA public, and at most the `r` low bits of `r3` secret. -/
def done (r : Nat) (τ : T) : Bool :=
  τ.ok && τ.nf == 0 && τ.sp == τ.W && τ.sec == 0 && scratch.all (pubR τ) && Nat.ble τ.lo r &&
    Impl.Scrub.PPC64LE.vregs.all (pubV τ) && τ.ca

end VG.PPC64LE.RTaint
