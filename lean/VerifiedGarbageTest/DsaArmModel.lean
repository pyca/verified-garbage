import Std.Data.HashMap
import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbageTest.Dsa

/-!
# Executing DSA's AArch64 programs in the ISA model

Development smoke tests use the ISA's execution and permission checks.
Memory and register closures are periodically flattened so multiword loops
do not accumulate a closure for every write. This evaluator is test-only;
no proof or emitted artifact depends on it.
-/
namespace VG.Test.DsaArmModel
open VG VG.AArch64

abbrev Words := Std.HashMap Nat (BitVec 64)

def memory (words : Words) : Mem := fun a =>
  BitVec.ofNat 8 (((words[a.toNat / 8]?.getD 0).toNat) >>> (8 * (a.toNat % 8)))

def registers : Array Reg := #[.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7,
  .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x19,
  .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

def flatten (s : State) (words : Words) : State :=
  let rs := registers.map s.gpr
  { s with gpr := fun r => rs[r.ctorIdx]!, mem := memory words }

structure Machine where
  state : State
  words : Words
  instructions : Nat := 0

def stores (i : Instr) (s : State) : List Nat :=
  let region := match i with
    | .str sz _ r off => some (s.gpr r + BitVec.ofNat 64 off, sz.bits / 8)
    | .strb _ r off => some (s.gpr r + BitVec.ofNat 64 off, 1)
    | _ => none
  match region with
  | none => []
  | some (a, n) => ((List.range ((a.toNat + n - 1) / 8 - a.toNat / 8 + 1)).map (a.toNat / 8 + ·))

def block (is : List Instr) (machine : Machine) : Except String Machine := do
  let mut s := machine.state
  let mut dirty := []
  for i in is do
    dirty := stores i s ++ dirty
    let some next := isa.exec i s | throw s!"instruction fault: {reprStr i}"
    s := next
  let mut words := machine.words
  for index in dirty do
    words := words.insert index (s.mem.readW (BitVec.ofNat 64 (8 * index)) 64)
  return ⟨flatten s words, words, machine.instructions + is.length⟩

def evaluate : Nat → Prog isa → Machine → Except String Machine
  | 0, _, _ => .error "model execution exhausted fuel"
  | _ + 1, .block is, m => block is m
  | fuel + 1, .seq a b, m => (evaluate fuel a m).bind (evaluate fuel b)
  | fuel + 1, .ite c a b, m => do
    let some taken := isa.eval c m.state | throw "undefined branch condition"
    evaluate fuel (if taken then a else b) m
  | fuel + 1, .loop body c, m => do
    let m' ← evaluate fuel body m
    let some again := isa.eval c m'.state | throw "undefined loop condition"
    if again then evaluate fuel (.loop body c) m' else pure m'
  | _, .call .., _ => .error "unexpected call in inline baseline model test"
  | _, .icall .., _ => .error "unexpected indirect call in baseline model test"
  | _, .frame .., _ => .error "unexpected stack frame in baseline model test"

end VG.Test.DsaArmModel
