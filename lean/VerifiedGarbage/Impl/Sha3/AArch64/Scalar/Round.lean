module

public import VerifiedGarbage.Impl.Sha3.AArch64.Lanes

/-!
# Keccak-f[1600] on AArch64: two rounds in general registers

The 25 lanes are in registers throughout (`Lanes.lean`). `eor` and `bic`
rotate their second operand at no cost, so ρ's rotations are left pending:
the register of lane
`i` holds the lane rotated right by `pend i`, and each
XOR or AND-NOT rotates one operand by the difference. What an output lane's
register is then pending is up to the code: `B ⊕ (¬B' ∧ B'')` may be computed
in the rotation pending on `B` or on `B''`. `pend` picks one of the two for
each lane so that every lane is pending the same rotation after the round as
before it: the choices make a tree rooted at lane 0, whose rotation is 0.
(`pend` was found by a breadth-first search from lane 0.) So a round has no
rotation instruction, 100 `eor`s and `bic`s in all, and all rounds have the
same code up to the registers' two arrangements.

θ needs the five column parities and one more register besides the lanes'.
The registers `temps` are free, `nt` of them; the lanes of column 1 that rows `5 - ns … 4` use
(`ns = 6 - nt`) are stored where `spill` says, after their parity is computed,
and loaded again where θ is applied to them, just before their row.
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Scalar

open VG.AArch64
open VG.Impl.Sha3 (rhoOff)
open VG.Impl.Sha3.AArch64.Lanes

/-- The rotation right pending on lane `i`. -/
def pend (i : Nat) : Nat :=
  [0, 18, 33, 0, 33, 28, 38, 18, 28, 18, 56, 31, 49, 31, 49, 60, 0, 41, 56, 23, 31, 19, 21, 31, 19].getD i 0

/-- The register of home `i` (not `x16` and `x17`, which a call may change). -/
def lreg (i : Nat) : Reg :=
  [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
    .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27].getD i .x0

/-- Lane `i`'s register before round `r`. -/
def reg (r i : Nat) : Reg := lreg (home r i)

/-- `d = n ⊕ ROR(m, k)`, `k` modulo 64. -/
def eor (d n m : Reg) (k : Nat) : Instr :=
  if k % 64 = 0 then .logic .eor .x d n m else .logicRor .eor .x d n m (k % 64)

/-- `d = n ∧ ¬ROR(m, k)`, `k` modulo 64. -/
def bic (d n m : Reg) (k : Nat) : Instr := .bicRor .x d n m (k % 64)

/-- The rotation that takes a word pending `a` to pending `b`. -/
def turn (a b : Nat) : Nat := b + 64 - a % 64

/-- How a lane is stored and loaded again. -/
structure Spill where
  save : Nat → Reg → Instr
  load : Nat → Reg → Instr

/-- The code of two rounds, with the free registers `temps`; with ρ's rotations
left pending (`lazy`), or done. -/
structure Conf where
  temps : List Reg
  lazy : Bool
  sp : Spill

namespace Conf
variable (c : Conf)

/-- The rotation pending on lane `i` between rounds. -/
def pd (i : Nat) : Nat := if c.lazy then pend i else 0

/-- The number of free registers. -/
def nt : Nat := c.temps.length

/-- The number of lanes spilled. -/
def ns : Nat := 6 - c.nt

/-- The slot of row `y`'s spilled lane, if it has one. -/
def slot (y : Nat) : Option Nat := if 5 - c.ns ≤ y then some (y - (5 - c.ns)) else none

/-- The registers the parities and `D₀` are computed in: the free ones, then
those of the spilled lanes. -/
def work (r k : Nat) : Reg :=
  if k < c.nt then c.temps.getD k .x0 else reg r (rowSrc (5 - c.ns + (k - c.nt)) 1)

/-- The place of column `x` in the order the parities are computed in: 1, 0, 2, 3, 4. -/
def place (x : Nat) : Nat := if x = 1 then 0 else if x = 0 then 1 else x

/-- The register of column `x`'s parity. -/
def par (r x : Nat) : Reg := c.work r (place x)

/-- The parity of column `x`, pending what its lane 0 is. -/
def parity (r x : Nat) : List Instr :=
  (if c.nt ≤ place x then [c.sp.save (place x - c.nt) (c.work r (place x))] else []) ++
  ([eor (c.par r x) (reg r x) (reg r (x + 5)) (turn (c.pd (x + 5)) (c.pd x))] : List Instr) ++
  ([2, 3, 4].map fun y => eor (c.par r x) (c.par r x) (reg r (x + 5 * y)) (turn (c.pd (x + 5 * y)) (c.pd x)))

/-- The register of `Dₓ`, over a parity that is not needed any more (but `D₀`, in a register of its own). -/
def dreg (r x : Nat) : Reg :=
  if x = 0 then c.work r 5 else if x = 2 then c.par r 1 else if x = 4 then c.par r 3
  else if x = 1 then c.par r 0 else c.par r 2

/-- `Dₓ`, pending what parity `x - 1` is. -/
def dcol (r x : Nat) : Instr :=
  eor (c.dreg r x) (c.par r ((x + 4) % 5)) (c.par r ((x + 1) % 5)) (turn (c.pd ((x + 1) % 5) + 1) (c.pd ((x + 4) % 5)))

/-- θ on lane `i` (and ρ, where it is not left pending), from `n` to `d`. -/
def theta (r i : Nat) (d n : Reg) : List Instr :=
  [eor d n (c.dreg r (i % 5)) (turn (c.pd ((i + 4) % 5)) (c.pd i))] ++
  if c.lazy || rhoOff i == 0 then [] else [.ror .x d d (64 - rhoOff i)]

/-- The registers free in row `y`: the working registers that are not a
spilled lane's of this row or an earlier one, written again. -/
def spare (r y : Nat) : List Reg :=
  ([c.par r 4, c.dreg r 0, c.dreg r 2, c.dreg r 3, c.dreg r 4].filter fun a =>
    (List.range (y + 1)).all fun z => a != reg r (rowSrc z 1)) ++
  if y = 4 then [c.dreg r 1] else []

/-- What `Bₖ` of row `y` is pending. -/
def bpend (y k : Nat) : Nat := if c.lazy then (c.pd (rowSrc y (k % 5)) + rhoOff (rowSrc y (k % 5))) % 64 else 0

/-- Row `y`: χ, over the registers of the row's inputs. -/
def row (r y : Nat) : List Instr :=
  let T := (c.spare r y).getD 0 .x0
  let t := (c.spare r y).getD 1 .x0
  let u := (c.spare r y).getD 2 .x0
  let b (k : Nat) : Reg := if k % 5 = 1 then T else reg r (rowSrc y (k % 5))
  let a (k : Nat) : Reg := reg r (rowSrc y k)
  let nb (d : Reg) (k : Nat) : Instr := bic d (b (k + 2)) (b (k + 1)) (turn (c.bpend y (k + 1)) (c.bpend y (k + 2)))
  let fin (d : Reg) (k : Nat) (n : Reg) : Instr :=
    if c.bpend y k = c.pd (rowOut y k) then eor d (b k) n (turn (c.bpend y (k + 2)) (c.bpend y k))
    else eor d n (b k) (turn (c.bpend y k) (c.bpend y (k + 2)))
  (match c.slot y with
    | some j => ([c.sp.load j T] : List Instr) ++ c.theta r (rowSrc y 1) T T
    | none => c.theta r (rowSrc y 1) T (a 1)) ++
  ([nb t 1, nb u 2, nb (a 1) 3, fin (a 1) 3 (a 1), nb (a 3) 4, fin (a 3) 4 (a 3), fin (a 4) 2 u,
    nb u 0, fin (a 2) 1 t, fin (a 0) 0 u] : List Instr)

/-- A round but for ι: `r` is 0 or 1, its place in the loop's body. -/
def round (r : Nat) : List Instr :=
  [1, 0, 2, 3, 4].flatMap (c.parity r) ++
  (if c.nt ≤ 5 then [c.sp.save (5 - c.nt) (c.work r 5)] else []) ++
  [0, 2, 4, 1, 3].map (c.dcol r) ++
  ([0, 2, 3, 4].flatMap fun x => (List.range 5).flatMap fun y =>
    c.theta r (x + 5 * y) (reg r (x + 5 * y)) (reg r (x + 5 * y))) ++
  (List.range 5).flatMap (c.row r)

end Conf

/-- The register of lane 0 is the same before every round (ι's operand). -/
theorem reg_zero : ∀ r < 2, reg r 0 = .x0 := by decide

end VG.Impl.Sha3.AArch64.Scalar
