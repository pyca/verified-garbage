import Std.Data.HashMap
import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbageTest.Dsa

/-!
# Executing DSA's x86-64 programs in the ISA model

Development smoke tests use the ISA's execution and permission checks.
Memory and register closures are periodically flattened so multiword loops
do not accumulate a closure for every write. This evaluator is test-only;
no proof or emitted artifact depends on it.
-/
namespace VG.Test.DsaModel
open VG VG.X86_64

abbrev Words := Std.HashMap Nat (BitVec 64)

def memory (words : Words) : Mem := fun a =>
  BitVec.ofNat 8 (((words[a.toNat / 8]?.getD 0).toNat) >>> (8 * (a.toNat % 8)))

def registers : Array Reg :=
  #[.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

def vectors : Array XReg :=
  #[.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7,
    .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14, .xmm15]

def flatten (s : State) (words : Words) : State :=
  let rs := registers.map s.gpr
  let xs := vectors.map s.xmm
  { s with gpr := fun r => rs[r.ctorIdx]!, xmm := fun r => xs[r.ctorIdx]!, mem := memory words }

structure Machine where
  state : State
  words : Words
  instructions : Nat := 0

def stores (i : Instr) (s : State) : List Nat :=
  let region := match i with
    | .store p _ => some (s.ea p, 8)
    | .store32 p _ => some (s.ea p, 4)
    | .store8 p _ => some (s.ea p, 1)
    | .movdquStore p _ => some (s.ea p, 16)
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
  | _, .call .., _ => .error "unexpected call in inline baseline model test"
  | _, .icall .., _ => .error "unexpected indirect call in baseline model test"
  | _, .frame .., _ => .error "unexpected stack frame in baseline model test"

def wordBytes (n : Nat) : List Byte := (List.range 8).map fun i => BitVec.ofNat 8 (n >>> (8 * i))

def initial (v : Dsa.Vector) (pLen qLen : Nat) (signing : Bool) : Except String Machine := do
  let key := Spec.Dsa.encodeBE pLen v.params.p ++ Spec.Dsa.encodeBE qLen v.params.q ++
    Spec.Dsa.encodeBE pLen v.params.g ++ Spec.Dsa.encodeBE pLen v.y ++
    (if signing then Spec.Dsa.encodeBE qLen v.x else [])
  let nonce := Spec.Dsa.encodeBE qLen v.k
  let digest ← Dsa.digest v
  let signature := Spec.Dsa.encodeBE qLen v.sig.r ++ Spec.Dsa.encodeBE qLen v.sig.s
  let stack := wordBytes 0 ++ (if signing then
    [qLen, 0x2200, digest.length, 0x10000, 16 * pLen] else [0x2200, digest.length, 0x10000, 16 * pLen]).flatMap wordBytes
  let regions := [(0x1000, key), (0x2000, nonce), (0x2200, digest), (0x2400, signature), (0x20000, stack)]
  let mem : Mem := fun a =>
    match regions.find? (fun (p, bs) => p ≤ a.toNat && a.toNat < p + bs.length) with
    | some (p, bs) => bs.getD (a.toNat - p) 0
    | none => if (0x10000 ≤ a.toNat && a.toNat < 0x10000 + 128 * pLen) ||
        (0x3000 ≤ a.toNat && a.toNat < 0x3040) then 0xa5 else 0
  let args := if signing then #[0x3000, 2 * qLen, 0x1000, key.length, pLen, 0x2000]
    else #[0x1000, key.length, pLen, qLen, 0x2400, signature.length]
  let s : State := {
    gpr := fun r => if r = .rsp then 0x20000 else
      if r = .rdi then BitVec.ofNat 64 args[0]! else if r = .rsi then BitVec.ofNat 64 args[1]! else
      if r = .rdx then BitVec.ofNat 64 args[2]! else if r = .rcx then BitVec.ofNat 64 args[3]! else
      if r = .r8 then BitVec.ofNat 64 args[4]! else if r = .r9 then BitVec.ofNat 64 args[5]! else
      BitVec.ofNat 64 (0x123400 + r.ctorIdx)
    cf := none, zf := none, sf := none, of := none, mem := mem
    rd := [⟨0x1000, key.length⟩, ⟨0x2000, nonce.length⟩, ⟨0x2200, digest.length⟩, ⟨0x2400, signature.length⟩]
    wr := [⟨0x3000, 2 * qLen⟩, ⟨0x10000, 128 * pLen⟩, ⟨0x20000, stack.length⟩] }
  let mut words : Words := {}
  for index in [:0x20100 / 8] do
    let value := mem.readW (BitVec.ofNat 64 (8 * index)) 64
    if value != 0 then words := words.insert index value
  return ⟨flatten s words, words, 0⟩

def check (v : Dsa.Vector) (pLen qLen : Nat) (signing : Bool) (expectedSuccess : Bool := true) : Except String Nat := do
  let before ← initial v pLen qLen signing
  let program := if signing then Impl.Dsa.X86_64.SignVerify.sign (Impl.Bignum.X86_64.Public.mm Impl.Bignum.X86_64.Public.aY Impl.Bignum.X86_64.Public.aY
      Impl.Bignum.X86_64.Public.aY) Impl.Bignum.X86_64.Public.mm
    else Impl.Dsa.X86_64.SignVerify.verify (Impl.Bignum.X86_64.Public.mm Impl.Bignum.X86_64.Public.aY Impl.Bignum.X86_64.Public.aY
      Impl.Bignum.X86_64.Public.aY) Impl.Bignum.X86_64.Public.mm
  let after ← evaluate 20000 program before
  unless after.state.gpr .rax == BitVec.ofNat 64 expectedSuccess.toNat do
    throw "unexpected success/failure result"
  for reg in Impl.Bignum.X86_64.saved ++ [.rsp] do
    unless after.state.gpr reg == before.state.gpr reg do throw s!"ABI register changed: {reprStr reg}"
  if signing then
    let expected := if expectedSuccess then
      Spec.Dsa.encodeBE qLen v.sig.r ++ Spec.Dsa.encodeBE qLen v.sig.s else List.replicate (2 * qLen) 0
    unless Spec.Rsa.bytesAt after.state.mem 0x3000 (2 * qLen) == expected do
      throw "signature differs from NIST"
  return after.instructions

/-- Differential checks of the actual arithmetic programs on padded odd
composite moduli. The expected values come from the mathematical operations,
not hand-authored signature vectors. -/
def arithmeticChecks : Except String Nat := do
  let mut total := 0
  for modulus in [257, 289, 65535] do
    let v : Dsa.Vector := {
      params := ⟨modulus, modulus, 2 ^ 127 + 17⟩
      hash := "SHA-256", x := 2 ^ 126 + 31, k := 19 }
    let before ← initial v 16 16 true
    let before := { before with state := { before.state with
      wr := [⟨0x3000, 32⟩, ⟨0x10000, 16384⟩, ⟨0x20000, 48⟩] } }
    let setup := Impl.Bignum.X86_64.seqs [.block Impl.Dsa.X86_64.SignVerify.signEntry,
      Impl.Dsa.X86_64.SignVerify.workspaces]
    let before ← evaluate 20000 setup before
    let mul := Impl.Bignum.X86_64.Public.mm
    let pow := Impl.Dsa.X86_64.Core.pow (mul Impl.Bignum.X86_64.Public.aY Impl.Bignum.X86_64.Public.aY
      Impl.Bignum.X86_64.Public.aY) mul Impl.Dsa.Layout.pWorkspace
      Impl.Dsa.X86_64.Core.generator Impl.Dsa.X86_64.Core.nonce
      (Impl.Dsa.X86_64.Core.element Impl.Dsa.Layout.t)
    let product := Impl.Dsa.X86_64.Core.product mul Impl.Dsa.Layout.qWorkspace
      Impl.Dsa.X86_64.Core.generator Impl.Dsa.X86_64.Core.privateScalar
      (Impl.Dsa.X86_64.Core.scalar Impl.Dsa.Layout.t)
    let reduce := Impl.Dsa.X86_64.Core.reduce mul Impl.Dsa.X86_64.Core.generator
      (Impl.Dsa.X86_64.Core.scalar Impl.Dsa.Layout.t)
    let empty := Impl.Bignum.X86_64.seqs [.block [.mov32 .rax (.imm 0),
      .store (Impl.Dsa.X86_64.Core.field .digestPrefixLen) .rax],
      Impl.Dsa.X86_64.Core.reduce mul Impl.Dsa.X86_64.Core.digest
        (Impl.Dsa.X86_64.Core.scalar Impl.Dsa.Layout.t)]
    for (name, program, expected) in [
        ("power", pow, Spec.Dsa.powMod v.params.g v.k modulus),
        ("product", product, v.params.g * v.x % modulus),
        ("reduction", reduce, v.params.g % modulus), ("empty reduction", empty, 0)] do
      let after ← evaluate 20000 program before
      let actual := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt after.state.mem
        (BitVec.ofNat 64 (0x10000 + Impl.Dsa.Layout.t)) 16)
      unless actual == expected do throw s!"{name} mismatch modulo {modulus}: {actual} != {expected}"
      total := total + after.instructions - before.instructions
    for value in [0, 1, modulus - 1, modulus, modulus + 1, 2 ^ 127 + 17] do
      let sample := { v with params := { v.params with g := value } }
      let start ← initial sample 16 16 true
      let start := { start with state := { start.state with
        wr := [⟨0x3000, 32⟩, ⟨0x10000, 16384⟩, ⟨0x20000, 48⟩] } }
      let prepared ← evaluate 20000 setup start
      for aboveOne in [false, true] do
        let program := Impl.Bignum.X86_64.seqs [
          .block [.mov .rax (.imm (-1)), .store (Impl.Dsa.X86_64.Core.field .mask) .rax],
          Impl.Dsa.X86_64.Checks.range Impl.Dsa.Layout.pWorkspace
            Impl.Dsa.X86_64.Core.generator aboveOne]
        let after ← evaluate 20000 program prepared
        let actual := after.state.mem.readW
          (BitVec.ofNat 64 (0x10000 + Impl.Dsa.Layout.Field.mask.offset)) 64
        let valid := (if aboveOne then 1 else 0) < value && value < modulus
        let expected : BitVec 64 := if valid then -1 else 0
        unless actual == expected do throw s!"range mask mismatch for {value}, modulus={modulus}, aboveOne={aboveOne}"
        total := total + after.instructions - prepared.instructions
  for value in [0, 1, 127, 128, 255, 256, 65535, 2 ^ 127] do
    let sample : Dsa.Vector := { params := ⟨value, 257, 2⟩, hash := "SHA-256" }
    let before ← initial sample 16 16 true
    let before := { before with state := { before.state with gpr := fun r =>
      if r == .rsi then 0x1000 else if r == .rcx then 16 else before.state.gpr r } }
    let after ← evaluate 20000 Impl.Dsa.X86_64.Checks.significant before
    let width := (Spec.Dsa.bitLength value + 7) / 8
    let head := value >>> (8 * (width - 1))
    unless after.state.gpr .r8 == BitVec.ofNat 64 width &&
        after.state.gpr .r9 == BitVec.ofNat 64 head do
      throw s!"actual-width scan mismatch for {value}"
    total := total + after.instructions
  return total

end VG.Test.DsaModel

/-- Run a published case through the whole ISA program. From lean/:
`lake env lean --run VerifiedGarbageTest/DsaModel.lean [p_bits] [q_bits] [sign|verify|both]`.
The default is 1024/160, both operations. These are slow model checks;
they complement, and do not replace, whole-operation proofs and native tests. -/
def main (args : List String) : IO Unit := do
  if args[0]? == some "arithmetic" then
    match VG.Test.DsaModel.arithmeticChecks with
    | .ok n => IO.println s!"Padded-modulus arithmetic, scalar-range and actual-width checks passed ({n} instructions)"
    | .error e => throw (IO.userError e)
    return
  let bits := (args[0]?.getD "1024").toNat?.getD 1024
  let qbits := (args[1]?.getD (if bits == 1024 then "160" else "256")).toNat?.getD 256
  let mode := args[2]?.getD "both"
  let text ← IO.FS.readFile "../vectors/nist-cavp-dsa/SigGen.txt"
  let .ok cases := VG.Test.Dsa.parse text true | throw (IO.userError "DSA vector parse failed")
  let some v := cases.find? (fun v => VG.Spec.Dsa.bitLength v.params.p == bits &&
    VG.Spec.Dsa.bitLength v.params.q == qbits) | throw (IO.userError "no matching NIST DSA vector")
  let stdout ← IO.getStdout
  for signing in [true, false] do
    if mode == "both" || mode == (if signing then "sign" else "verify") then
      stdout.putStrLn s!"Running NIST {bits}/{qbits}, signing={signing}"
      stdout.flush
      let start ← IO.monoMsNow
      match VG.Test.DsaModel.check v (bits / 8) (qbits / 8) signing with
      | .ok n => stdout.putStrLn s!"Passed {n} modeled instructions in {(← IO.monoMsNow) - start} ms"
      | .error e => throw (IO.userError e)
      let invalid := { v with params := { v.params with p := v.params.p - 1 } }
      match VG.Test.DsaModel.check invalid (bits / 8) (qbits / 8) signing false with
      | .ok _ => stdout.putStrLn "Malformed-domain rejection, ABI preservation and failure output passed"
      | .error e => throw (IO.userError e)
      stdout.flush
