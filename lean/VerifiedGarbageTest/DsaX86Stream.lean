import VerifiedGarbageTest.DsaX86Mont
import VerifiedGarbage.Impl.Dsa.X86.Stream
import VerifiedGarbage.Impl.Dsa.X86.Bytes
import VerifiedGarbage.Proof.Dsa.X86.Stream
import VerifiedGarbage.Proof.Dsa.X86.Bytes
import VerifiedGarbage.Proof.Dsa.X86.StreamTiming
import VerifiedGarbage.Proof.Dsa.X86.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86.ArithmeticTiming
import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Dsa.X86.ChecksTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreLoad
import VerifiedGarbage.Proof.Dsa.X86.Minus
import VerifiedGarbage.TCB.Axioms

/-! Synthetic differential tests of complete big-endian reduction and the
shared fixed-width component decoder. -/

#assert_standard_axioms VG.Proof.Dsa.X86.reduceStream_ok
#assert_standard_axioms VG.Proof.Dsa.X86.reduceStream_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.loadComponent_ok
#assert_standard_axioms VG.Proof.Dsa.X86.storeComponent_ok

#assert_standard_axioms VG.Proof.Dsa.X86.ordinaryMul_ok
#assert_standard_axioms VG.Proof.Dsa.X86.ordinaryAdd_ok
#assert_standard_axioms VG.Proof.Dsa.X86.ordinaryMul_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.ordinaryAdd_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.nonzero_ok
#assert_standard_axioms VG.Proof.Dsa.X86.lessThan_ok
#assert_standard_axioms VG.Proof.Dsa.X86.equal_ok
#assert_standard_axioms VG.Proof.Dsa.X86.checkRange_ok
#assert_standard_axioms VG.Proof.Dsa.X86.equal_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.checkRange_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.coreLoadSlot_ok
#assert_standard_axioms VG.Proof.Dsa.X86.modulusMinus_ok

namespace VG.Test.DsaX86Stream
open VG VG.X86 VG.Test.DsaX86Mont VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

/-- Reduce the `len` bytes of `value`, with the length an immediate or
(`saved`) a word of the workspace. -/
def check (n modulus len value : Nat) (saved : Bool := false) : Except String Unit := do
  let base := 0x10000
  let size := contextBytes n
  let input := base + size + 256
  let ws := (List.range (size / 4)).foldl (fun w i =>
    w.insert (base / 4 + i) (0xa5a5a5a5 : BitVec 32)) ({} : Words)
  let lenWord := 20
  let ws := put (put ws (base + slot n 0) (2 * n) modulus) (base + lenWord) 1 len
  let encoded := (List.range len).foldl (fun a i =>
    a + ((value >>> (8 * (len - 1 - i))) % 256) * 2 ^ (8 * i)) 0
  let ws := put ws input ((len + 3) / 4) encoded
  let state : State := {
    gpr := fun r => if r == .edi then BitVec.ofNat 32 base else BitVec.ofNat 32 (0xdead00 + r.ctorIdx)
    cf := none, zf := none, sf := none, of := none
    mem := memory ws, rd := [⟨BitVec.ofNat 64 input, len⟩], wr := [⟨BitVec.ofNat 64 base, size⟩] }
  let initialized ← evaluate fuel (contextSetup n) ⟨state, ws⟩
  let src : Src := if saved then .mem (VG.Impl.Mont.X86.sc lenWord) else .imm (BitVec.ofNat 32 len)
  let streamState : State := { initialized.state with
    gpr := fun r => if r == .esi then BitVec.ofNat 32 input else initialized.state.gpr r }
  let result ← evaluate fuel (reduceStream n src) ⟨streamState, initialized.words⟩
  unless get result.words (base + slot n 6) (2 * n) == value % 2 ^ (8 * len) % modulus do
    throw s!"streaming reduction mismatch: n={n}, modulus={modulus}, len={len}, value={value}"
  for i in [0, 3, 4] do
    unless get result.words (base + slot n i) (2 * n) == get initialized.words (base + slot n i) (2 * n) do
      throw "arithmetic constant changed"
  unless get result.words (base + lenWord) 1 == len do throw "saved length changed"
  unless get result.words input ((len + 3) / 4) == encoded do throw "input changed"
  if 4 ≤ len && len ≤ 8 * n && len % 4 == 0 then
    let loadState : State := { initialized.state with gpr := fun r => if r == .esi then BitVec.ofNat 32 input else initialized.state.gpr r }
    let loaded ← evaluate fuel (loadComponent len n (slot n 5)) ⟨loadState, initialized.words⟩
    unless get loaded.words (base + slot n 5) (2 * n) == value % 2 ^ (8 * len) do
      throw "component decoder mismatch"

def checkArithmetic (n modulus a b : Nat) : Except String Unit := do
  let base := 0x10000
  let size := contextBytes n
  let ws := put (put (put ({} : Words) (base + slot n 0) (2 * n) modulus)
    (base + slot n 5) (2 * n) a) (base + slot n 8) (2 * n) b
  let state : State := {
    gpr := fun r => if r == .edi then BitVec.ofNat 32 base else 0
    cf := none, zf := none, sf := none, of := none
    mem := memory ws, rd := [], wr := [⟨BitVec.ofNat 64 base, size⟩] }
  let initialized ← evaluate fuel (contextSetup n) ⟨state, ws⟩
  for amount in [0, 1, 2, modulus] do
    let subtracted ← evaluate fuel (modulusMinus n amount) initialized
    unless get subtracted.words (base + slot n 6) (2 * n) == modulus - amount do
      throw "modulus subtraction mismatch"
  let result ← evaluate fuel (ordinaryMul n) initialized
  unless get result.words (base + slot n 6) (2 * n) == a * b % modulus do
    throw s!"ordinary multiplication mismatch: n={n}, a={a}, b={b}"
  if a < modulus && b < modulus then
    let sum ← evaluate fuel (ordinaryAdd n) initialized
    unless get sum.words (base + slot n 6) (2 * n) == (a + b) % modulus do
      throw "ordinary addition mismatch"
  let nz ← evaluate fuel (nonzero n (slot n 5)) initialized
  unless nz.state.gpr .edx == (if a == 0 then 0 else BitVec.allOnes 32) do
    throw "nonzero mask mismatch"
  let lt ← evaluate fuel (lessThan n (slot n 5) (slot n 8)) initialized
  unless lt.state.gpr .eax == (if a < b then BitVec.allOnes 32 else 0) do
    throw "less-than mask mismatch"
  let eq ← evaluate fuel (equal n (slot n 5) (slot n 8)) initialized
  unless eq.state.gpr .edx == (if a == b then BitVec.allOnes 32 else 0) do
    throw "equality mask mismatch"
  for mask in [0, 2 ^ 32 - 1] do
    let fw := put initialized.words (base + 24) 1 mask
    let fs : State := { initialized.state with mem := memory fw }
    let ranged ← evaluate fuel (checkRange n (slot n 5) (slot n 8) 24) ⟨fs, fw⟩
    unless get ranged.words (base + 24) 1 == (if 0 < a && a < b then mask else 0) do
      throw "range accumulation mismatch"

def checks : Except String Unit := do
  for (n, m) in [(1, 9), (1, 2 ^ 64 - 59), (3, 2 ^ 160 - 47), (4, 2 ^ 256 - 189)] do
    for (a, b) in [(0, 0), (0, 1), (1, 0), (m - 1, m - 1), (2 ^ (64 * n) - 1, m + 1)] do
      checkArithmetic n m a b
  for len in [0, 1, 4, 7, 8, 20, 32] do
    check 1 257 len (2 ^ (8 * len) - 1)
  check 3 (2 ^ 160 - 47) 20 (2 ^ 160 - 1)
  check 3 (2 ^ 160 - 47) 17 (2 ^ 136 - 5) (saved := true)
  check 1 257 0 0 (saved := true)
  check 3 (2 ^ 160 - 47) 384 (2 ^ 3072 - 1)
  check 4 (2 ^ 256 - 189) 28 1

end VG.Test.DsaX86Stream

run_cmd
  match VG.Test.DsaX86Stream.checks with
  | .ok _ => pure ()
  | .error e => Lean.throwError e
