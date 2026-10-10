import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated

/-! Reproduce the untrusted allocated instruction lists. Run from lean/ with
`lake env lean --run GenerateP256Verify.lean`. The generated lists become
production code only through the separate kernel-checked certificates. -/
open VG VG.AArch64 VG.Impl.P256 VG.Impl.Ecdsa.AArch64

private def render (code : List Instr) : String := Id.run do
  let mut s := (reprStr code).replace "VG.AArch64.Instr." "."
  s := s.replace "(VG.AArch64.Size.x)" ".x"
  for i in [:31] do
    s := s.replace s!"(VG.AArch64.Reg.x{i})" s!".x{i}"
  for op in ["and","orr","eor"] do
    s := s.replace s!"(VG.AArch64.LogicOp.{op})" s!".{op}"
  return "aarch64_instrs% " ++ s

def main : IO Unit := do
  let cases := [("doubleRR",VerifyArithmetic.Kind.doubleRR),("mixedHead",.mixedHead),
    ("mixedTail",.mixedTail),("jacTail",.jacTail),("cachedHead",.cachedHead)]
  let mut text := "import VerifiedGarbage.TCB.AArch64.Isa\nimport VerifiedGarbage.Impl.AArch64Instrs\n\n/-! Lean-generated output of VerifyRegisters.optimize. These literal instruction\nblocks are untrusted input to the checked arithmetic certificates. -/\nnamespace VG.Impl.P256.VerifyAllocatedCode\nopen VG VG.AArch64\n\n"
  for (name,k) in cases do
    let code := VerifyRegisters.optimize [] VerifyRegisters.pool (VerifyAllocated.keep k) (VerifyAllocated.raw k)
    text := text ++ "def " ++ name ++ " : List Instr :=\n" ++ render code ++ "\n\n"
  let inverse := VerifyRegisters.optimize [.x4,.x5,.x6,.x7]
    (VerifyRegisters.pool.filter (· != .x1)) (fun _ => true)
    (.movz .x .x12 0 0 :: p256.invN.fgUpdate ++ p256.invN.abUpdate)
  text := text ++ "def inverseUpdate : List Instr :=\n" ++ render inverse ++
    "\n\nend VG.Impl.P256.VerifyAllocatedCode\n"
  IO.FS.writeFile "VerifiedGarbage/Impl/P256/VerifyAllocatedCode.lean" text
