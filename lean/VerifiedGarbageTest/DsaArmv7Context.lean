import VerifiedGarbageTest.DsaArmv7Mont
import VerifiedGarbage.Impl.Dsa.Arm.Context

/-! Synthetic differential and nesting tests for shared Montgomery setup. -/
namespace VG.Test.DsaArmv7Context
open VG VG.Arm VG.Impl.Mont.Arm.Dynamic VG.Test.DsaArmv7Mont

def check (n modulus : Nat) (asCall : Bool) : Except String Unit := do
  let base := 0x10000
  let size := contextBytes n
  let initial := machine n modulus base size fun w => put w (base + modS n) (2 * n) modulus
  let initial := { initial with state := { initial.state with
    gpr := fun r => if r == .r0 && !asCall then BitVec.ofNat 32 base else initial.state.gpr r
    unknowns := fun i => BitVec.ofNat 32 (0x90000000 + 4 * i) } }
  let result ← evaluate fuel
    (if asCall then Impl.Dsa.Arm.Context.call n else Impl.Dsa.Arm.Context.body n) initial
  unless get result.words (base + oneS n) (2 * n) == 1 do throw "one mismatch"
  unless get result.words (base + rrS n) (2 * n) == 2 ^ (128 * n) % modulus do throw "R-squared mismatch"
  unless (modulus * get result.words base 1 + 1) % 2 ^ 16 == 0 do throw "inverse mismatch"
  for r in (if asCall then [Reg.r11, .r12] else [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]) do
    unless result.state.gpr r == initial.state.gpr r do throw s!"register changed: {reprStr r}"
  unless result.state.sp == initial.state.sp do throw "stack pointer changed"
  for i in [:size / 4] do
    let d := 4 * i
    let changed := (Impl.Dsa.Arm.Context.scratch n).any fun (o, k) => o ≤ d && d < o + k
    unless changed || get result.words (base + d) 1 == get initial.words (base + d) 1 do
      throw s!"write outside setup scratch at {d}"

def checks : Except String Unit := do
  for n in [1, 3, 4] do
    for modulus in [3, 257, 2 ^ (64 * n) - 59] do
      check n modulus false
      check n modulus true

end VG.Test.DsaArmv7Context

run_cmd
  match VG.Test.DsaArmv7Context.checks with
  | .ok _ => pure ()
  | .error e => Lean.throwError e
