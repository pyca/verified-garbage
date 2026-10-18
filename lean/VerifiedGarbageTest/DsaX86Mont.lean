import Std.Data.HashMap
import VerifiedGarbage.Impl.Mont.X86.Dynamic
import VerifiedGarbage.Impl.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.X86.DynamicOps
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.TCB.Axioms

/-!
Execute the runtime-modulus arithmetic in the x86 ISA model and compare it
with natural-number modular arithmetic. These are synthetic differential
tests, not DSA known-answer vectors. The proof audits are independent of the
executable test runner.
-/

#assert_standard_axioms VG.Proof.Mont.X86.Dynamic.mul_ok
#assert_standard_axioms VG.Proof.Mont.X86.Dynamic.setupInverse_ok

namespace VG.Test.DsaX86Mont
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

abbrev Words := Std.HashMap Nat (BitVec 32)

def memory (words : Words) : Mem := fun a =>
  BitVec.ofNat 8 ((words[a.toNat / 4]?.getD 0).toNat >>> (8 * (a.toNat % 4)))

def registers : Array Reg := #[.eax, .ecx, .edx, .ebx, .esp, .ebp, .esi, .edi]

structure Machine where
  state : State
  words : Words

def block (is : List Instr) (m : Machine) : Except String Machine := do
  let mut state := m.state
  let mut words := m.words
  for i in is do
    let some next := isa.exec i state | throw s!"instruction fault: {reprStr i}"
    if let .store dst _ := i then
      let a := state.ea dst
      unless a.toNat % 4 == 0 do throw "unaligned test store"
      words := words.insert (a.toNat / 4) (next.mem.readW a 32)
    if let .store8 dst _ := i then
      let a := state.ea dst
      let aligned := BitVec.ofNat 64 (a.toNat / 4 * 4)
      words := words.insert (a.toNat / 4) (next.mem.readW aligned 32)
    let rs := registers.map next.gpr
    state := { next with gpr := fun r => rs[r.ctorIdx]!, mem := memory words }
  return ⟨state, words⟩

/-- Materialize words written by the model's call or frame push, just as
`block` materializes instruction stores. -/
def pushedMachine (before : Machine) (after : State) : Machine :=
  let low := (after.gpr .esp).toNat
  let count := ((before.state.gpr .esp).toNat - low) / 4
  let words := (List.range count).foldl (fun ws i =>
    let a := BitVec.ofNat 64 (low + 4 * i)
    ws.insert (low / 4 + i) (after.mem.readW a 32)) before.words
  ⟨{ after with mem := memory words }, words⟩

/-- Enough steps for every loop of the tests. -/
def fuel : Nat := 1000000000

def evaluate : Nat → Prog isa → Machine → Except String Machine
  | 0, _, _ => .error "model execution exhausted fuel"
  | _ + 1, .block is, m => block is m
  | fuel + 1, .seq a b, m => (evaluate fuel a m).bind (evaluate fuel b)
  | fuel + 1, .ite c a b, m => do
    let some taken := isa.eval c m.state | throw "undefined branch condition"
    evaluate fuel (if taken then a else b) m
  | fuel + 1, .loop body c, m => do
    let next ← evaluate fuel body m
    let some again := isa.eval c next.state | throw "undefined loop condition"
    if again then evaluate fuel (.loop body c) next else pure next
  | fuel + 1, .call _ body, m => do
    let some entered := isa.call m.state | throw "call fault"
    let result ← evaluate fuel body (pushedMachine m entered)
    let some returned := isa.ret entered result.state | throw "return fault"
    pure ⟨returned, result.words⟩
  | fuel + 1, .frame push body pop, m => do
    let some entered := isa.push push m.state | throw "frame push fault"
    let result ← evaluate fuel body (pushedMachine m entered)
    let some returned := isa.pop pop entered result.state | throw "frame pop fault"
    pure ⟨returned, result.words⟩

def put (words : Words) (address count value : Nat) : Words :=
  (List.range count).foldl (fun ws i => ws.insert (address / 4 + i)
    (BitVec.ofNat 32 (value >>> (32 * i)))) words

def get (words : Words) (address count : Nat) : Nat :=
  ((List.range count).reverse).foldl (fun v i =>
    2 ^ 32 * v + (words[address / 4 + i]?.getD 0).toNat) 0

def check (n modulus a b out base : Nat) : Except String Unit := do
  let size := 6000
  let inv := 0
  let mo := 64
  let ao := 1024
  let bo := 2048
  let tmp := 3072
  let acc := 4096
  let M : Impl.Mont.Mod := { n := n, mo := mo, tmp := tmp, minv := 0 }
  let words := (List.range (size / 4)).foldl (fun w i =>
    w.insert (base / 4 + i) (0xa5a5a5a5 : BitVec 32)) ({} : Words)
  let words := put (put (put words (base + mo) (2 * n) modulus)
    (base + ao) (2 * n) a) (base + bo) (2 * n) b
  let state : State := {
    gpr := fun r => if r == .edi then BitVec.ofNat 32 base else BitVec.ofNat 32 (0xdead00 + r.ctorIdx)
    cf := none, zf := none, sf := none, of := none
    mem := memory words, rd := [], wr := [⟨BitVec.ofNat 64 base, size⟩] }
  let initialized ← block (setupInverse mo inv) ⟨state, words⟩
  unless (modulus * get initialized.words (base + inv) 1 + 1) % 2 ^ 32 == 0 do
    throw "inverse mismatch"
  let result ← evaluate fuel (mul M inv acc out ao bo) initialized
  let v := get result.words (base + out) (2 * n)
  unless v < modulus && v * 2 ^ (64 * n) % modulus == a * b % modulus do
    throw s!"Montgomery mismatch: n={n}, modulus={modulus}, a={a}, b={b}, output={out}"
  for r in [.edi, .esi, .esp] do
    unless result.state.gpr r == state.gpr r do throw "preserved register changed"
  for offset in [:size / 4] do
    let d := 4 * offset
    unless (out ≤ d && d < out + 8 * n) || (tmp ≤ d && d < tmp + 8 * n) ||
        (acc ≤ d && d < acc + 4 * (4 * n + 1)) do
      unless result.words[(base + d) / 4]? == initialized.words[(base + d) / 4]? do
        throw s!"memory outside frame changed: {d}"

def checks : Except String Nat := do
  let mut count := 0
  -- Padded scalar widths, in every layout.
  for n in [1, 3, 4] do
    for modulus in [3, 2 ^ (64 * n - 1) + 1, 2 ^ (64 * n) - 1] do
      for (a, b) in [(0, 0), (modulus - 1, modulus - 1), (2 ^ (64 * n) - 1, 1)] do
        for out in [512, 1024, 2048] do
          check n modulus a b out 0x10000
          count := count + 1
  -- All supported DSA p widths (the loops do not depend on the layout).
  for n in [16, 32, 48] do
    for modulus in [2 ^ (64 * n - 1) + 1, 2 ^ (64 * n) - 1] do
      check n modulus (modulus - 1) (modulus - 1) 1024 0x10000
      count := count + 1
  -- Exercise address arithmetic near the upper end of the 32-bit address space.
  check 48 (2 ^ 3072 - 3) (2 ^ 3072 - 4) (2 ^ 3072 - 4) 1024 0xffff0000
  return count + 1

end VG.Test.DsaX86Mont

run_cmd
  match VG.Test.DsaX86Mont.checks with
  | .ok _ => pure ()
  | .error e => Lean.throwError e
