import VerifiedGarbageTest.DsaArmv7Mont
import VerifiedGarbage.Impl.Dsa.Arm.PublicValidation

/-! Synthetic differential tests of nested validation calls and their register saves. -/
namespace VG.Test.DsaArmv7PublicValidation
open VG VG.Arm VG.Test.DsaArmv7Mont

def putBE (words : Words) (address len value : Nat) : Words := Id.run do
  let mut words := words
  for i in [:len] do
    let a := address + i
    let shift := 8 * (a % 4)
    let old := words[a / 4]?.getD 0
    let byte := BitVec.ofNat 32 (value / 256 ^ (len - 1 - i) % 256)
    words := words.insert (a / 4) ((old &&& ~~~(255#32 <<< shift)) ||| (byte <<< shift))
  return words

def check (pLen qLen p q g y mask : Nat) : Except String Unit := do
  let base := 0x1000
  let key := 0x10000
  let mut words : Words := {}
  for (d, a) in [(64, key), (68, key + pLen), (72, key + pLen + qLen), (76, key + 2 * pLen + qLen)] do
    words := put words (base + d) 1 a
  words := put words (base + 116) 1 mask
  for i in [:9] do words := put words (base + 128 + 4 * i) 1 (0xabcdef00 + i)
  words := putBE words key pLen p
  words := putBE words (key + pLen) qLen q
  words := putBE words (key + pLen + qLen) pLen g
  words := putBE words (key + 2 * pLen + qLen) pLen y
  let s : State := {
    gpr := fun r => match r with
      | .r0 => BitVec.ofNat 32 base
      | .r1 => 2048
      | .r2 => BitVec.ofNat 32 key
      | .r3 => BitVec.ofNat 32 (3 * pLen + qLen)
      | _ => BitVec.ofNat 32 (0x12340000 + r.ctorIdx)
    sp := 0x30000, n := false, z := false, c := false, v := false
    mem := memory words
    unknowns := fun i => BitVec.ofNat 32 (0x90000000 + 8 * i)
    rd := [⟨BitVec.ofNat 64 key, 3 * pLen + qLen⟩]
    wr := [⟨BitVec.ofNat 64 base, 16384⟩] }
  let result ← evaluate fuel (Impl.Dsa.Arm.PublicValidation.body pLen qLen) ⟨s, words⟩
  let valid := 1 < g && g < p && 1 < y && y < p && (p - 1) % q == 0 && powMod g q p == 1 && powMod y q p == 1
  unless get result.words (base + 116) 1 == (if valid then mask else 0) do throw "validation mask mismatch"
  let mut exponent := 0
  for i in [:qLen] do
    exponent := 256 * exponent + (result.state.mem (BitVec.ofNat 64 (base + 14912 + i))).toNat
  unless exponent == q - 2 do throw "inverse exponent mismatch"
  for r in [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] do
    unless result.state.gpr r == s.gpr r do throw s!"callee-saved register changed: {reprStr r}"
  unless result.state.sp == s.sp do throw "stack pointer changed"
  for i in [:9] do
    unless get result.words (base + 128 + 4 * i) 1 == 0xabcdef00 + i do throw "outer register save overwritten"

def checks : Except String Unit := do
  -- 1543 = 6 * 257 + 1; 64 is in the order-257 subgroup.
  for mask in [0, 0x5a5a5a5a, 0xffffffff] do
    check 8 4 1543 257 64 64 mask
    check 8 4 1543 257 1 64 mask
    check 8 4 1543 257 64 1543 mask
    check 8 4 1543 257 64 2 mask
    check 8 4 1545 257 64 64 mask

end VG.Test.DsaArmv7PublicValidation

run_cmd
  match VG.Test.DsaArmv7PublicValidation.checks with
  | .ok _ => pure ()
  | .error e => Lean.throwError e
