import VerifiedGarbage.Impl.P384.EcdhDouble
import VerifiedGarbage.Impl.P256.VerifyRegisters

/-! Reproduce the untrusted P-384 ECDH allocations from lean/ with
`lake env lean --run GenerateP384Ecdh.lean`. Certificates check the output. -/
open VG VG.AArch64 VG.Impl.P384 VG.Impl.P384.EcdhDouble VG.Impl.P256.VerifyRegisters

private def render (code : List Instr) : String := Id.run do
  let mut s := (reprStr code).replace "VG.AArch64.Instr." "."
  s := s.replace "(VG.AArch64.Size.x)" ".x"
  for i in [:31] do
    s := s.replace s!"(VG.AArch64.Reg.x{i})" s!".x{i}"
  for op in ["and","orr","eor"] do
    s := s.replace s!"(VG.AArch64.LogicOp.{op})" s!".{op}"
  return "aarch64_instrs% " ++ s

private def allocated (a b : VG.Impl.Weierstrass.Pt) : IO (List Instr) := do
  let some (items, values) := ssa [] (raw a b) | throw (IO.userError "ssa failed")
  let some code := allocate [] regs (schedule (stores (keep b) items) values) values spill
    | throw (IO.userError "allocation failed")
  return code

def main : IO Unit := do
  let cases := [("doubleRD", ← allocated K.R K.D), ("doubleDR", ← allocated K.D K.R)]
  let mut text := "module\n\npublic import VerifiedGarbage.TCB.AArch64.Isa\npublic import VerifiedGarbage.Impl.AArch64Instrs\n\n/-! Lean-generated register allocations of P-384's doublings (`Impl/P384/EcdhDouble.lean`),\nchecked independently against their raw arithmetic. -/\n\n@[expose] public section\n\nnamespace VG.Impl.P384.EcdhAllocatedCode\nopen VG VG.AArch64\n\n"
  for (name,code) in cases do
    text := text ++ "def " ++ name ++ " : List Instr :=\n" ++ render code ++ "\n\n"
  IO.FS.writeFile "VerifiedGarbage/Impl/P384/EcdhAllocatedCode.lean" (text++"end VG.Impl.P384.EcdhAllocatedCode\n")
