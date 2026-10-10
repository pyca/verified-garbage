import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Impl.P256.EcdhDouble
import VerifiedGarbage.Impl.P256.EcdhTable
import VerifiedGarbage.Impl.P256.VerifyRegisters

/-! Reproduce the untrusted P-256 ECDH allocations from lean/ with
`lake env lean --run GenerateP256Ecdh.lean`. Certificates check the output. -/
open VG VG.AArch64 VG.Impl.P256 VG.Impl.P256.VerifyRegisters
private instance : Inhabited Instr := ⟨.movz .x .x7 0 0⟩
private def ecdhSchedule (items : List Item) (values : Nat) : List Item := Id.run do
  let xs := items.toArray
  let deps := dependencies xs
  let mut successors := Array.replicate xs.size ([] : List Nat)
  for i in [:xs.size] do
    for d in deps[i]! do successors := successors.set! d (i :: successors[d]!)
  let mut scores := Array.replicate xs.size 0
  for i in (List.range xs.size).reverse do
    scores := scores.set! i ((match xs[i]!.instr with | .ldr .. => 4 | .mul .. | .umulh .. | .madd .. => 3 | _=>1) +
      (successors[i]!).foldl (fun n j => max n scores[j]!) 0)
  let mut counts := deps.map List.length
  let mut left := Array.replicate values 0
  for i in xs do
    for v in i.inputs do left := left.set! v (left[v]!+1)
  let mut live := Array.replicate values false
  let mut liveCount := 0
  let mut done := Array.replicate xs.size false
  let mut out := []
  for _ in [:xs.size] do
    let mut chosen := xs.size
    let mut best : Int := 0
    for j in [:xs.size] do
      if !done[j]! && counts[j]! == 0 then
        let i := xs[j]!
        let up := if i.dest.any (fun p => left[p.2]! > 0) then 1 else 0
        let down := (i.inputs.filter (fun v => left[v]! == 1)).length
        let pressure := (liveCount+up : Nat) - (down+27)
        let score : Int := Int.ofNat (scores[j]!) - Int.ofNat (1000*pressure)
        if chosen == xs.size || score > best then
          chosen := j
          best := score
    if chosen < xs.size then
      let i := xs[chosen]!
      out := i :: out
      done := done.set! chosen true
      for v in i.inputs do
        left := left.set! v (left[v]!-1)
        if left[v]! == 0 && live[v]! then
          live := live.set! v false
          liveCount := liveCount-1
      if let some (_,v) := i.dest then
        if left[v]! > 0 then
          live := live.set! v true
          liveCount := liveCount+1
      for j in successors[chosen]! do counts := counts.set! j (counts[j]!-1)
  return out.reverse


private def render (code : List Instr) : String := Id.run do
  let mut s := (reprStr code).replace "VG.AArch64.Instr." "."
  s := s.replace "(VG.AArch64.Size.x)" ".x"
  for i in [:31] do
    s := s.replace s!"(VG.AArch64.Reg.x{i})" s!".x{i}"
  for op in ["and","orr","eor"] do
    s := s.replace s!"(VG.AArch64.LogicOp.{op})" s!".{op}"
  return "aarch64_instrs% " ++ s

private def doubleCode : List Instr :=
  ((do
    let (items,values) ← ssa [] EcdhDouble.raw
    allocate [] pool (ecdhSchedule (stores EcdhDouble.keep items) values) values) : Option (List Instr)).getD EcdhDouble.raw

private def inverseUpdate : List Instr :=
  let p := VG.Impl.Ecdsa.AArch64.p256.invP
  let keep := fun off =>
    (p.sF≤off && off<p.sF+8*p.L) || (p.sG≤off && off<p.sG+8*p.L) ||
    (p.sA≤off && off<p.sA+8*p.M.n) || (p.sB≤off && off<p.sB+8*p.M.n)
  let regs := pool.filter fun r => r != .x1 && r != .x19 && r != .x20 && r != .x27
  VerifyRegisters.optimize [.x4,.x5,.x6,.x7] regs keep
    ([.movz .x .x12 0 0]++p.fgUpdate++p.abUpdate)

def main : IO Unit := do
  let cases := [("update",inverseUpdate),("double",doubleCode),("dblu",VerifyRegisters.optimize [] pool (EcdhTable.keep true) (EcdhTable.raw true)),("zaddu",VerifyRegisters.optimize [] pool (EcdhTable.keep false) (EcdhTable.raw false))]
  let mut text := "import VerifiedGarbage.TCB.AArch64.Isa\nimport VerifiedGarbage.Impl.AArch64Instrs\n\n/-! Lean-generated register allocations, checked independently against their raw arithmetic. -/\nnamespace VG.Impl.P256.EcdhAllocatedCode\nopen VG VG.AArch64\n\n"
  for (name,code) in cases do
    text := text ++ "def " ++ name ++ " : List Instr :=\n" ++ render code ++ "\n\n"
  IO.FS.writeFile "VerifiedGarbage/Impl/P256/EcdhAllocatedCode.lean" (text++"end VG.Impl.P256.EcdhAllocatedCode\n")
