import Std.Data.HashMap
import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
import VerifiedGarbage.Spec.MlKem

/-!
# ML-KEM's 16-bit AArch64 NTT in the ISA model

Runs `Ntt16.ntt` in the ISA model on polynomials and compares the result
with `Spec.MlKem.ntt`. Memory, general and vector registers are flattened
after every block so that the closures do not grow. Test-only.
-/
namespace VG.Test.MlKemNtt16Model
open VG VG.AArch64

abbrev Words := Std.HashMap Nat (BitVec 64)

def memory (words : Words) : Mem := fun a =>
  BitVec.ofNat 8 (((words[a.toNat / 8]?.getD 0).toNat) >>> (8 * (a.toNat % 8)))

def registers : Array Reg := #[.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7,
  .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x19,
  .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

def vregs : Array VReg := #[.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11,
  .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
  .v27, .v28, .v29, .v30, .v31]

def flatten (s : State) (words : Words) : State :=
  let rs := registers.map s.gpr
  let vs := vregs.map s.v
  { s with gpr := fun r => rs[r.ctorIdx]!, v := fun r => vs[r.ctorIdx]!, mem := memory words }

structure Machine where
  state : State
  words : Words
  instructions : Nat := 0

def stores (i : Instr) (s : State) : List Nat :=
  let region := match i with
    | .str sz _ r off => some (s.gpr r + BitVec.ofNat 64 off, sz.bits / 8)
    | .strb _ r off => some (s.gpr r + BitVec.ofNat 64 off, 1)
    | .strq _ r off => some (s.gpr r + BitVec.ofNat 64 off, 16)
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
  | _, .call .., _ => .error "unexpected call"
  | _, .frame .., _ => .error "unexpected frame"

/-- `f` (`u32`s) at `0x10000`, `scratch` (1024 bytes) at `0x20000`. -/
def start (f : List Nat) : Machine :=
  let words : Words := (List.range 128).foldl (fun w i =>
    w.insert (0x10000 / 8 + i) (BitVec.ofNat 64 (f.getD (2 * i) 0 + f.getD (2 * i + 1) 0 * 2 ^ 32)))
    {}
  let s : State := { gpr := fun r => if r = .x0 then 0x10000 else if r = .x1 then 0x20000 else 0
                     mem := memory words
                     sp := 0x40000
                     rd := [⟨0x10000, 1024⟩, ⟨0x20000, 1024⟩]
                     wr := [⟨0x10000, 1024⟩, ⟨0x20000, 1024⟩] }
  ⟨flatten s words, words, 0⟩

def coeffs (m : Machine) : List Nat :=
  (List.range 256).map fun i => (m.state.mem.readW (BitVec.ofNat 64 (0x10000 + 4 * i)) 32).toNat

def specNtt (f : List Nat) : List Nat :=
  (Spec.MlKem.ntt (Vector.ofFn fun i => (Fin.ofNat _ (f.getD i.val 0) : Spec.MlKem.Zq))).toList.map (·.val)

def specInv (f : List Nat) : List Nat :=
  (Spec.MlKem.nttInv (Vector.ofFn fun i => (Fin.ofNat _ (f.getD i.val 0) : Spec.MlKem.Zq))).toList.map (·.val)

def checkInv (f : List Nat) : Except String Nat := do
  let m ← evaluate 100 Impl.MlKem.AArch64.Ntt16.nttInv (start f)
  if coeffs m == specInv f then pure m.instructions
  else throw s!"mismatch: {(coeffs m).take 8} vs {(specInv f).take 8}"

def check (f : List Nat) : Except String Nat := do
  let m ← evaluate 100 Impl.MlKem.AArch64.Ntt16.ntt (start f)
  if coeffs m == specNtt f then pure m.instructions
  else throw s!"mismatch: {(coeffs m).take 8} vs {(specNtt f).take 8}"

/-- A deterministic pseudorandom polynomial. -/
def poly (seed : Nat) : List Nat :=
  (List.range 256).map fun i => (seed * 2654435761 + i * 40503 + (i * i) * 7919) % 3329

#eval check ((List.range 256).map fun _ => 3328)
#eval check ((List.range 256).map fun _ => 0)
#eval check (List.range 256)
#eval check (poly 1)
#eval check (poly 2)
#eval check (poly 3)

#eval checkInv ((List.range 256).map fun _ => 3328)
#eval checkInv ((List.range 256).map fun _ => 0)
#eval checkInv (List.range 256)
#eval checkInv (poly 1)
#eval checkInv (poly 2)
#eval checkInv (poly 3)

end VG.Test.MlKemNtt16Model
