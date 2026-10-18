import Std.Data.HashMap
import Lean.Elab.Command
import VerifiedGarbage.Impl.Mont.Arm.Context

/-!
Execute ARMv7's runtime-modulus arithmetic in the ISA model and compare it
with natural-number modular arithmetic. These are synthetic differential
tests, not DSA known-answer vectors.
-/

namespace VG.Test.DsaArmv7Mont
open VG VG.Arm VG.Impl.Mont.Arm.Dynamic

abbrev Words := Std.HashMap Nat (BitVec 32)

def memory (words : Words) : Mem := fun a =>
  BitVec.ofNat 8 ((words[a.toNat / 4]?.getD 0).toNat >>> (8 * (a.toNat % 4)))

def registers : Array Reg := #[.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

structure Machine where
  state : State
  words : Words

def block (is : List Instr) (m : Machine) : Except String Machine := do
  let mut state := m.state
  let mut words := m.words
  for i in is do
    let some next := isa.exec i state | throw s!"instruction fault: {reprStr i}"
    if let .str _ n off := i then
      let a := State.addr (state.gpr n + BitVec.ofNat 32 off)
      unless a.toNat % 4 == 0 do throw "unaligned test store"
      words := words.insert (a.toNat / 4) (next.mem.readW a 32)
    if let .strb _ n off := i then
      let a := State.addr (state.gpr n + BitVec.ofNat 32 off)
      let aligned := BitVec.ofNat 64 (a.toNat / 4 * 4)
      words := words.insert (a.toNat / 4) (next.mem.readW aligned 32)
    let rs := registers.map next.gpr
    state := { next with gpr := fun r => rs[r.ctorIdx]!, mem := memory words }
  return ⟨state, words⟩

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
    let some entry := isa.call m.state | throw "call fault"
    let next ← evaluate fuel body { m with state := entry }
    let some returned := isa.ret entry next.state | throw "return address changed"
    pure { next with state := returned }
  | _, .frame .., _ => .error "unexpected frame"

def put (words : Words) (address count value : Nat) : Words :=
  (List.range count).foldl (fun ws i => ws.insert (address / 4 + i)
    (BitVec.ofNat 32 (value >>> (32 * i)))) words

def get (words : Words) (address count : Nat) : Nat :=
  ((List.range count).reverse).foldl (fun v i =>
    2 ^ 32 * v + (words[address / 4 + i]?.getD 0).toNat) 0

/-- `-m⁻¹ mod 2¹⁶`. -/
def minv16 (m : Nat) : Nat := (List.range (2 ^ 16)).find? (fun x => (m * x + 1) % 2 ^ 16 == 0) |>.getD 0

def machine (n modulus base size : Nat) (extra : Words → Words) : Machine :=
  let words := (List.range (size / 4)).foldl (fun w i =>
    w.insert (base / 4 + i) (0xa5a5a5a5 : BitVec 32)) ({} : Words)
  let words := extra (put (put words (base + 64) (2 * n) modulus) base 1 (minv16 modulus))
  let state : State := {
    gpr := fun r => if r == .r12 then BitVec.ofNat 32 base else BitVec.ofNat 32 (0xdead00 + r.ctorIdx)
    sp := 0x8000, n := false, z := false, c := false, v := false
    mem := memory words, rd := [], wr := [⟨BitVec.ofNat 64 base, size⟩] }
  ⟨state, words⟩

def checkPreserved (s₀ s : State) : Except String Unit := do
  for r in [.r11, .r12, .lr] do
    unless s.gpr r == s₀.gpr r do throw "preserved register changed"

def checkMul (n modulus a b : Nat) : Except String Unit := do
  let base := 0x10000
  let size := 8000
  let tmp := 64 + 8 * n + 8
  let ao := 2048
  let bo := 3072
  let out := 4096
  let acc := 5000
  let M : Impl.Mont.Mod := { n := n, mo := 64, tmp := tmp, minv := 0 }
  let m₀ := machine n modulus base size fun w => put (put w (base + ao) (2 * n) a) (base + bo) (2 * n) b
  let r ← evaluate fuel (mul M 0 acc out ao bo) m₀
  let v := get r.words (base + out) (2 * n)
  unless v < modulus && v * 2 ^ (64 * n) % modulus == a * b % modulus do
    throw s!"Montgomery mismatch: n={n}, modulus={modulus}, a={a}, b={b}"
  checkPreserved m₀.state r.state

def checkAdd (n modulus a b : Nat) : Except String Unit := do
  let base := 0x10000
  let size := 8000
  let tmp := 64 + 8 * n + 8
  let ao := 2048
  let bo := 3072
  let out := 4096
  let acc := 5000
  let M : Impl.Mont.Mod := { n := n, mo := 64, tmp := tmp, minv := 0 }
  let m₀ := machine n modulus base size fun w => put (put w (base + ao) (2 * n) a) (base + bo) (2 * n) b
  let r ← evaluate fuel (addD M acc out ao bo) m₀
  unless get r.words (base + out) (2 * n) == (a + b) % modulus do
    throw s!"addition mismatch: n={n}, modulus={modulus}, a={a}, b={b}"
  checkPreserved m₀.state r.state

def powMod (a e m : Nat) : Nat := Id.run do
  let mut r := 1 % m
  let mut b := a % m
  let mut e := e
  while e > 0 do
    if e % 2 == 1 then r := r * b % m
    b := b * b % m
    e := e / 2
  return r

def checkExp (n modulus a e expWords : Nat) : Except String Unit := do
  let base := 0x10000
  let size := 8000
  let m₀ := machine n modulus base size fun w =>
    put (put (put (put w base 1 0x5a5a) (base + modS n) (2 * n) modulus) (base + baseS n) (2 * n) a)
      (base + expS n) expWords e
  let r ← evaluate fuel (contextSetup n) m₀
  unless (modulus * get r.words base 1 + 1) % 2 ^ 16 == 0 do throw s!"inverse mismatch: {modulus}"
  unless get r.words (base + rrS n) (2 * n) == 2 ^ (128 * n) % modulus do throw "R² mismatch"
  let r ← evaluate fuel (exponentiate n expWords) r
  unless get r.words (base + resS n) (2 * n) == powMod a e modulus do
    throw s!"exponentiation mismatch: n={n}, modulus={modulus}, a={a}, e={e}"
  unless r.state.gpr .r11 == m₀.state.gpr .r11 && r.state.gpr .r12 == m₀.state.gpr .r12 do
    throw "preserved register changed"

def checks : Except String Nat := do
  let mut count := 0
  for n in [1, 3, 4] do
    for modulus in [3, 2 ^ (64 * n - 1) + 1, 2 ^ (64 * n) - 1] do
      for (a, b) in [(0, 0), (modulus - 1, modulus - 1), (modulus - 1, 1), (1, modulus - 1)] do
        checkMul n modulus a b
        checkAdd n modulus a b
        count := count + 1
      checkMul n modulus (2 ^ (64 * n) - 1) 1
  for n in [16, 48] do
    let modulus := 2 ^ (64 * n) - 2 ^ 77 - 1
    checkMul n modulus (modulus - 1) (modulus - 2)
    checkAdd n modulus (modulus - 1) (modulus - 2)
    count := count + 1
  for n in [1, 3] do
    for modulus in [3, 2 ^ (64 * n - 1) + 1, 2 ^ (64 * n) - 1] do
      checkExp n modulus (modulus - 1) (2 ^ 64 - 3) 2
      checkExp n modulus 2 0 1
      checkExp n modulus (modulus / 3) (2 ^ 160 - 1) 5
  return count

end VG.Test.DsaArmv7Mont

run_cmd
  match VG.Test.DsaArmv7Mont.checks with
  | .ok _ => pure ()
  | .error e => Lean.throwError e
