module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Reordering straight-line RISC-V code

`sched ks c` is the instructions of `c` in another order: each `k` of `ks` in
turn takes the `k`-th instruction of those left, if it is independent of the
ones it passes; what is left then, or after `ks`, follows as it is. Two
instructions are independent if neither writes a register the other reads or
writes, and they do not both store, and if one stores and the other loads, they are at the same
base register and their doublewords do not overlap. So any `ks` whatever gives
code that runs as `c` does (`Proof/Framework/RISCV64/Sched.lean`): which order
it names is only a matter of speed, and an implementation states its code in
the order its proof reads best.

An instruction's registers are bits of a number, so that the kernel, which
evaluates `sched` once for each function's code, does it on numbers.
-/

@[expose] public section

namespace VG.Impl.Words.RISCV64

open VG.RISCV64

/-- What an instruction writes and reads (a bit for each register), and
whether it loads (1) or stores (2) a doubleword, at what base and offset. -/
structure Fp where
  w : Nat
  r : Nat
  k : Nat
  n : Nat
  off : Nat

/-- A register's bit. -/
def rbit (r : Reg) : Nat := 2 ^ r.ctorIdx

/-- An instruction's footprint, or none: such an instruction keeps its place. -/
def fp : Instr → Option Fp
  | .add d n m | .sub d n m | .sltu d n m | .mul d n m | .mulhu d n m | .logic _ d n m =>
    some ⟨rbit d, rbit n ||| rbit m, 0, 0, 0⟩
  | .addi d n _ | .addiw d n _ | .logicImm _ d n _ | .shift _ _ d n _ => some ⟨rbit d, rbit n, 0, 0, 0⟩
  | .li d _ | .lui d _ => some ⟨rbit d, 0, 0, 0, 0⟩
  | .load .d t n off => some ⟨rbit t, rbit n, 1, n.ctorIdx, off⟩
  | .store .d t n off => some ⟨0, rbit n ||| rbit t, 2, n.ctorIdx, off⟩
  | _ => none

/-- Whether the doublewords at two offsets from a base do not overlap. -/
def sepOff (a b : Nat) : Bool := (Nat.ble (a + 8) b && Nat.ble b 2048) || (Nat.ble (b + 8) a && Nat.ble a 2048)

/-- Whether two instructions' accesses to memory are independent. -/
def memOk (a b : Fp) : Bool :=
  Nat.ble (a.k + b.k) 2 || (Nat.beq (a.k + b.k) 3 && Nat.beq a.n b.n && sepOff a.off b.off)

/-- Whether two instructions are independent. -/
def indep (a b : Fp) : Bool :=
  Nat.beq (a.w &&& (b.r ||| b.w)) 0 && Nat.beq (b.w &&& a.r) 0 && memOk a b

/-- Whether an instruction, of footprint `f`, may pass those before it. -/
def passes (f : Fp) : List (Option Fp × Instr) → Bool
  | [] => true
  | (none, _) :: _ => false
  | (some a, _) :: l => indep a f && passes f l

/-- The instructions in the order `ks`. -/
def schedGo : List Nat → List (Option Fp × Instr) → List Instr
  | [], c => c.map (·.2)
  | k :: ks, c =>
    match c.drop k with
    | [] => c.map (·.2)
    | x :: rest =>
      match x.1 with
      | none => c.map (·.2)
      | some f =>
        match passes f (c.take k) with
        | true => x.2 :: schedGo ks (c.take k ++ rest)
        | false => c.map (·.2)

/-- The instructions of `c` in the order `ks`. -/
def sched (ks : List Nat) (c : List Instr) : List Instr := schedGo ks (c.map fun i => (fp i, i))

end VG.Impl.Words.RISCV64
