import VerifiedGarbage.Impl.Dsa.X86.GenerateKey
import VerifiedGarbage.Impl.Dsa.X86.Generate
import VerifiedGarbage.Impl.Dsa.X86.Generation.Entry
import VerifiedGarbage.Impl.Mont.X86.Window
import VerifiedGarbage.TCB.X86.Print
import Lean

/- Unproven experiments. No Artifact, Verified value, or exported proof is constructed. -/
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
namespace Prototype

def seq (xs : List (Prog isa)) : Prog isa := xs.foldr .seq (.block [])
def imm (n : Nat) : Src := .imm (BitVec.ofNat 32 n)
def copyBetween (count src dst : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (imm 0)]) (.loop (.block [
    .mov .eax (.mem (at_ .esi src)), .store (at_ .ebp dst) .eax,
    .alu .add .esi (imm 4), .alu .add .ebp (imm 4),
    .alu .add .ecx (imm 1), .alu .cmp .ecx (imm count)]) .ne)

/-- Copy the original context to a private stack arena, retaining the original
context for the caller; only the ordinary result is copied back. -/
def stackPower (n _e : Nat) (power : Prog isa) : Prog isa :=
  let bytes := contextBytes n + 128 * n
  .frame (.push [.edi])
    (.frame (.alloc bytes) (seq [
      .block [.mov .esi (.reg .edi), .mov .ebp (.reg .esp)],
      copyBetween (contextBytes n / 4) 0 0,
      .block [.mov .edi (.reg .esp)], power,
      .block [.mov .esi (.reg .edi), .mov .ebp (.mem (at_ .esp bytes))],
      copyBetween (2 * n) (slot n 6) (slot n 6)]) (.free bytes)) (.pop .edi 1)

/-- Direct table selection is used only for public exponents. -/
def publicSelect (n tab dst : Nat) : Prog isa := seq [
  .block [.mov .eax (.mem (sc windowOffset)), .mov .edx (imm (8*n)), .mul .edx,
    .alu .add .eax (.reg .edi), .alu .add .eax (imm tab),
    .mov .ecx (.reg .eax), .mov .ebp (.reg .edi), .mov .ebx (imm (2*n))],
  .loop (.block [.mov .eax (.mem (at_ .ecx 0)), .store (at_ .ebp dst) .eax,
    .alu .add .ecx (imm 4), .alu .add .ebp (imm 4), .alu .sub .ebx (imm 1)]) .ne]

partial def same : Prog isa → Prog isa → Bool
  | .block a, .block b => decide (a=b)
  | .seq a b, .seq c d => same a c && same b d
  | .ite c a b, .ite d e f => decide (c=d) && same a e && same b f
  | .loop a c, .loop b d => decide (c=d) && same a b
  | .frame a b c, .frame d e f => decide (a=d) && decide (c=f) && same b e
  | .call a _, .call b _ => a == b
  | _, _ => false

partial def replace (rules : List (Prog isa × Prog isa)) (p : Prog isa) : Prog isa :=
  match rules.find? (fun r => same p r.1) with
  | some r => r.2
  | none => match p with
    | .seq a b => .seq (replace rules a) (replace rules b)
    | .ite c a b => .ite c (replace rules a) (replace rules b)
    | .loop a c => .loop (replace rules a) c
    | .frame a b c => .frame a (replace rules b) c
    | x => x

partial def publicCalls (p : Prog isa) : Prog isa := match p with
  | .seq a b => .seq (publicCalls a) (publicCalls b)
  | .ite c a b => .ite c (publicCalls a) (publicCalls b)
  | .loop a c => .loop (publicCalls a) c
  | .frame a b c => .frame a (publicCalls b) c
  | .call n b => .call (if n.startsWith "vg_dsa_pow_" then n ++ "_public" else n) b
  | x => x

def window (n e : Nat) (pub : Bool) : Prog isa :=
  let tab := contextBytes n
  let p := windowExponentiate n e tab
  stackPower n e (if pub then replace [(selectWindow n tab (slot n 7), publicSelect n tab (slot n 7))] p else p)

def widths := [(16,5),(3,5),(32,5),(32,7),(4,7),(32,8),(4,8),(48,8)]
def domains := [(128,20),(256,28),(256,32),(384,32),(256,20)]
def hash (bits : Nat) (suffix : String) : VG.Impl.Pbkdf2.Stream.X86.Hash :=
  ⟨64, if bits=160 then 84 else 96, bits/8, bits/8, 20,
    (if bits=160 then "vg_sha1_init" else "vg_sha256_init"), .block [],
    (if bits=160 then "vg_sha1_update_scratch" else "vg_sha256_update_scratch") ++ suffix, .block [],
    (if bits=160 then "vg_sha1_finalize_scratch" else "vg_sha256_finalize_scratch") ++ suffix, .block []⟩

/-- Experimental row kernel: hold the multiplier in ESI and amortize pointer
control over a public chunk. Save ESI because the enclosing power owns it. -/
def rowCandidate (chunk : Nat) (p : Prog isa) : Option (Prog isa) := do
  let .seq start (.seq (.loop (.block is) .ne) tail) := p | none
  let some (Instr.mov .eax (.mem mult)) := is[0]? | none
  let some (Instr.mov .edx (.mem input)) := is[1]? | none
  let some (Instr.alu .add .eax (.mem output)) := is[3]? | none
  let some (Instr.alu .add .eax (.imm width)) := is[21]? | none
  let n := width.toNat / 4
  if n == 0 || !same start (.block [.mov .ebx (imm 0), .mov .ecx (.reg .edi)]) ||
      !same (.block is) (.block (mulStepW n output.disp input.disp mult.disp)) then none
  else
    let k := if chunk == 0 then n else if n % chunk == 0 then chunk else 2
    let mac := (List.range k).flatMap fun j => [
      .mov .eax (.mem (at_ .ecx (input.disp + 4*j))), .mul .esi,
      .alu .add .eax (.mem (at_ .ebp (output.disp + 4*j))), .alu .adc .edx (imm 0),
      .alu .add .eax (.reg .ebx), .alu .adc .edx (imm 0),
      .store (at_ .ebp (output.disp + 4*j)) .eax, .mov .ebx (.reg .edx)]
    some (.frame (.push [.esi]) (seq [start, .block [.mov .esi (.mem mult)],
      .loop (.block (mac ++ [.alu .add .ecx (imm (4*k)), .alu .add .ebp (imm (4*k)),
        .mov .eax (.reg .edi), .alu .add .eax (imm (4*n)), .alu .cmp .ecx (.reg .eax)])) .ne,
      tail]) (.pop .esi 1))

partial def rows (chunk : Nat) (p : Prog isa) : Prog isa :=
  match rowCandidate chunk p with
  | some r => r
  | none => match p with
    | .seq a b => .seq (rows chunk a) (rows chunk b)
    | .ite c a b => .ite c (rows chunk a) (rows chunk b)
    | .loop a c => .loop (rows chunk a) c
    | .frame a b c => .frame a (rows chunk b) c
    | x => x

def functions (dedup win pub : Bool) : List (String × Prog isa) := Id.run do
  let mut fs := []
  let check := VG.Impl.Dsa.X86.Generate.checkParameters
  if pub then fs := fs ++ [("vg_dsa_check_parameters", publicCalls check)]
  if dedup then
    let derive := replace (domains.map fun (p,q) => (VG.Impl.Dsa.X86.Generate.parameters p q, .block []))
      VG.Impl.Dsa.X86.Generate.deriveKey
    fs := fs ++ [("proto_dsa_derive_prevalidated", derive),
      ("vg_dsa_generate_key", VG.Impl.Dsa.X86.GenerateKey.code "vg_dsa_check_parameters"
        "proto_dsa_derive_prevalidated" check derive)]
  for (n,e) in widths do
    if win then fs := fs ++ [(VG.Impl.Dsa.X86.Pow.name n e, seq [.block VG.Impl.Dsa.X86.Pow.save,
      contextSetup n, window n e false, .block VG.Impl.Dsa.X86.Pow.restore])]
    if pub then fs := fs ++ [(VG.Impl.Dsa.X86.Pow.name n e ++ "_public", seq [.block VG.Impl.Dsa.X86.Pow.save,
      contextSetup n, window n e true, .block VG.Impl.Dsa.X86.Pow.restore])]
  if pub then
    let rules := [(3,5),(4,8),(16,32),(32,64),(48,96),(16,5),(32,8),(48,8)].map fun (n,e) =>
      (exponentiate n e, window n e true)
    for (s1,s256,suffix) in [("","",""),("","_shani","_sha256_shani"),
        ("_shani","","_sha1_shani"),("_shani","_shani","_sha1_shani_sha256_shani")] do
      fs := fs ++ [("vg_dsa_generate_parameters" ++ suffix,
        replace rules (VG.Impl.Dsa.X86.Generation.code (hash 160 s1) (hash 256 s256)
          "vg_dsa_check_parameters" check))]
  return fs

end Prototype

def main (args : List String) : IO Unit := do
  let mode := args.head!
  let fs := Prototype.functions (mode.contains 'd') (mode.contains 'w') (mode.contains 'p')
  let json := fs.map fun (name, p) =>
    let p := if mode.contains 'r' then Prototype.rows ((args[1]?).getD "4" |>.toNat!) p else p
    let lines := VG.X86.printer.function p
    let calls := lines.filterMap fun l => match l with | .call n => some n | _ => none
    let assembly := String.intercalate "\n" (lines.map fun l => match l with
      | .text s => s | .call n => "call {" ++ n ++ "}" | .sym .. => "UNSUPPORTED_SYMBOL")
    Lean.Json.mkObj [("name", Lean.toJson name), ("assembly", Lean.toJson (assembly ++ "\n.p2align 6")),
      ("calls", Lean.toJson calls.eraseDups)]
  IO.println (Lean.Json.arr json.toArray).compress
