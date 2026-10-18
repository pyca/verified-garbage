import VerifiedGarbageTest.DsaArmv7Mont
import VerifiedGarbage.Impl.Dsa.Arm.Stream

/-! Synthetic differential tests of the counted modular-doubling loop. -/
namespace VG.Test.DsaArmv7Doubling
open VG VG.Arm VG.Impl.Mont.Arm VG.Test.DsaArmv7Mont

def check (n modulus value count : Nat) : Except String Unit := do
  let base := 0x10000
  let size := contextBytes n
  let initial := machine n modulus base size fun w =>
    put (put w (base + modS n) (2 * n) modulus) (base + resS n) (2 * n) value
  let result ← evaluate fuel (Impl.Dsa.Arm.doubles n count) initial
  unless get result.words (base + resS n) (2 * n) == 2 ^ count * value % modulus do
    throw s!"doubling mismatch: n={n}, modulus={modulus}, value={value}, count={count}"
  checkPreserved initial.state result.state
  unless result.state.sp == initial.state.sp do throw "stack pointer changed"
  for i in [:size / 4] do
    let offset := 4 * i
    let changed := (resS n ≤ offset && offset < resS n + 8 * n) ||
      (tmpS n ≤ offset && offset < tmpS n + 8 * n) ||
      (accS n ≤ offset && offset < accS n + 4 * (8 * n + 2))
    unless changed || get result.words (base + offset) 1 == get initial.words (base + offset) 1 do
      throw s!"write outside arithmetic scratch at {offset}"

def checks : Except String Unit := do
  -- Exercise zero iterations, both outcomes of modular subtraction, and
  -- carries across halfwords, words, and the most significant word.
  for (n, modulus) in [(1, 257), (1, 2 ^ 64 - 59), (2, 2 ^ 127 + 123)] do
    for value in [0, 1, modulus / 2, modulus / 2 + 1, modulus - 1] do
      for count in [0, 1, 8, 17] do check n modulus value count

end VG.Test.DsaArmv7Doubling

run_cmd
  match VG.Test.DsaArmv7Doubling.checks with
  | .ok _ => pure ()
  | .error e => Lean.throwError e
