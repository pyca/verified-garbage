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

/-- A triangular raw product, doubled, plus the diagonal, followed by the
existing Montgomery reduction rows. This is an unproven square experiment. -/
def fastSquare (compact deferred : Bool) (n o a : Nat) : Prog isa :=
  let N := 2*n
  let acc := slot n 2
  let cross := (List.range (N-1)).map fun i => seq [
    .block [.mov .esi (.mem (sc (a+4*i))), .mov .ebx (imm 0),
      .mov .ecx (.reg .edi), .alu .add .ecx (imm (4*(i+1))),
      .mov .ebp (.reg .edi), .alu .add .ebp (imm (4*(2*i+1)))],
    .loop (.block [.mov .eax (.mem (at_ .ecx a)), .mul .esi,
      .alu .add .eax (.mem (at_ .ebp acc)), .alu .adc .edx (imm 0),
      .alu .add .eax (.reg .ebx), .alu .adc .edx (imm 0),
      .store (at_ .ebp acc) .eax, .mov .ebx (.reg .edx),
      .alu .add .ecx (imm 4), .alu .add .ebp (imm 4),
      .mov .eax (.reg .edi), .alu .add .eax (imm (4*N)), .alu .cmp .ecx (.reg .eax)]) .ne,
    .block [.store (sc (acc+4*(i+N))) .ebx]]
  let compactCross := .frame (.alloc 4) (seq [
    .block [.mov .eax (imm 0), .store (at_ .esp 0) .eax],
    .loop (seq [
      .block [.mov .eax (.mem (at_ .esp 0)), .mov .ecx (.reg .edi), .alu .add .ecx (.reg .eax),
        .mov .esi (.mem (at_ .ecx a)), .alu .add .ecx (imm 4), .mov .ebp (.reg .ecx),
        .alu .add .ebp (.reg .eax), .mov .ebx (imm 0)],
      .loop (.block [.mov .eax (.mem (at_ .ecx a)), .mul .esi,
        .alu .add .eax (.mem (at_ .ebp acc)), .alu .adc .edx (imm 0),
        .alu .add .eax (.reg .ebx), .alu .adc .edx (imm 0),
        .store (at_ .ebp acc) .eax, .mov .ebx (.reg .edx),
        .alu .add .ecx (imm 4), .alu .add .ebp (imm 4),
        .mov .eax (.reg .edi), .alu .add .eax (imm (4*N)), .alu .cmp .ecx (.reg .eax)]) .ne,
      .block [.store (at_ .ebp acc) .ebx, .mov .eax (.mem (at_ .esp 0)), .alu .add .eax (imm 4),
        .store (at_ .esp 0) .eax, .alu .cmp .eax (imm (4*(N-1)))]]) .ne]) (.free 4)
  let diagonal := seq [
    .block [.mov .ecx (.reg .edi), .mov .ebp (.reg .edi), .mov .ebx (imm 0)],
    .loop (.block [.mov .eax (.mem (at_ .ecx a)), .mov .edx (.reg .eax), .mul .edx,
      .alu .add .eax (.reg .ebx), .alu .adc .edx (imm 0),
      .alu .add .eax (.mem (at_ .ebp acc)), .alu .adc .edx (.mem (at_ .ebp (acc+4))),
      .alu .sbb .ebx (.reg .ebx), .alu .and .ebx (imm 1),
      .store (at_ .ebp acc) .eax, .store (at_ .ebp (acc+4)) .edx,
      .alu .add .ecx (imm 4), .alu .add .ebp (imm 8),
      .mov .eax (.reg .edi), .alu .add .eax (imm (4*N)), .alu .cmp .ecx (.reg .eax)]) .ne]
  -- A full raw product needs carry propagation through every remaining high
  -- word; the CIOS row's two-word tail assumes those farther words are zero.
  let fullRow := seq [
    .block [.mov .ebx (imm 0), .mov .ecx (.reg .edi)],
    .loop (.block (mulStepW N acc (slot n 0) (slot n 1))) .ne,
    .block [.mov .eax (.mem (at_ .ebp acc)), .alu .add .eax (.reg .ebx),
      .store (at_ .ebp acc) .eax, .alu .sbb .ebx (.reg .ebx),
      .mov .ecx (.reg .ebp), .alu .add .ecx (imm 4), .alu .sub .ebp (imm (4*N))],
    .loop (.block [.mov .eax (.mem (at_ .ecx acc)), .alu .add .ebx (.reg .ebx),
      .alu .adc .eax (imm 0), .store (at_ .ecx acc) .eax, .alu .sbb .ebx (.reg .ebx),
      .alu .add .ecx (imm 4), .mov .eax (.reg .edi), .alu .add .eax (imm (4*(2*N+1))),
      .alu .cmp .ecx (.reg .eax)]) .ne]
  let deferredRow := seq [
    .block [.mov .ebx (imm 0), .mov .ecx (.reg .edi)],
    .loop (.block (mulStepW N acc (slot n 0) (slot n 1))) .ne,
    .block [.mov .eax (.mem (at_ .ebp acc)), .alu .add .eax (.reg .ebx),
      .mov .edx (imm 0), .alu .adc .edx (imm 0),
      .alu .add .eax (.mem (sc 8)), .alu .adc .edx (imm 0),
      .store (at_ .ebp acc) .eax, .store (sc 8) .edx,
      .alu .sub .ebp (imm (4*N))]]
  let red := seq [
    .block [.mov .eax (imm 0), .store (sc 8) .eax, .mov .ebp (.reg .edi)],
    .loop (seq [.block (redDigit acc 0 (slot n 1)),
      (if deferred then deferredRow else fullRow),
      .block [.alu .add .ebp (imm 4), .mov .edx (.reg .edi),
        .alu .add .edx (imm (4*N)), .alu .cmp .ebp (.reg .edx)]]) .ne,
    (if deferred then .block [.mov .eax (.mem (sc 8)), .store (sc (acc+8*N)) .eax] else .block []),
    csubW (contextMod n) (acc+4*N) o]
  .frame (.push [.esi]) (seq ([zerosW acc (2*N+1)] ++ (if compact then [compactCross] else cross) ++
    [chainW .adc (2*N) acc acc acc, diagonal, red])) (.pop .esi 1)

/-- Fixed-address masked table scan, accumulating each output word in a
register. Masks are computed once per window, without secret indexing. -/
def wordSelect (n tab dst : Nat) : Prog isa :=
  .frame (.alloc 64) (seq [
    .block ((List.range 16).flatMap fun j => windowMask j ++ [.store (at_ .esp (4*j)) .ecx]),
    .block [.mov .ebp (.reg .edi)],
    .loop (.block ([.mov .ebx (imm 0)] ++ (List.range 16).flatMap (fun j => [
      .mov .eax (.mem (at_ .ebp (entry n tab j))), .alu .and .eax (.mem (at_ .esp (4*j))),
      .alu .or .ebx (.reg .eax)]) ++ [
      .store (at_ .ebp dst) .ebx, .alu .add .ebp (imm 4),
      .mov .eax (.reg .edi), .alu .add .eax (imm (8*n)), .alu .cmp .ebp (.reg .eax)])) .ne]) (.free 64)

/-- Public high-bit fast paths seed a reduced power of two immediately.
The original setup remains the fallback for other modulus shapes. -/
def fastSeed (n : Nat) : Prog isa := Id.run do
  let mut p := contextSeed n
  for top in (List.range (2*n)).reverse do
    let above := (List.range (2*n-top-1)).flatMap fun j =>
      [.alu .or .ebx (.mem (sc (slot n 0 + 4*(top+1+j))))]
    let test := .block ([.mov .ebx (imm 0)] ++ above ++ [
      .mov .eax (.mem (sc (slot n 0 + 4*top))), .shift .shr .eax 31,
      .alu .xor .eax (imm 1), .alu .or .eax (.reg .ebx), .alu .cmp .eax (imm 0)])
    let seed := seq [
      .block (setupInverse (slot n 0) 0), one n (slot n 3), zerosW (slot n 4) (2*n),
      .block [.mov .eax (imm 2147483648), .store (sc (slot n 4 + 4*top)) .eax,
        .mov .esi (imm (65*n-(32*top+31)))],
      doubleLoop (contextMod n) (slot n 2) (slot n 4)]
    -- Only the common full-width and padded DSA q shapes need a branch.
    if top == 2*n-1 || (n==3 && top==4) || (n==4 && top==6) then
      p := .seq test (.ite .e seed p)
  return p

def squareRules (compact deferred : Bool) : List (Prog isa × Prog isa) :=
  [3,4,16,32,48].flatMap fun n => [4,5,6].map fun i =>
    (mul (contextMod n) 0 (slot n 2) (slot n i) (slot n i) (slot n i),
      fastSquare compact deferred n (slot n i) (slot n i))

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
    let p := if mode.contains 'f' then Prototype.replace ([3,4,16,32,48].map fun n => (contextSeed n, Prototype.fastSeed n)) p else p
    let p := if mode != "baseline" && mode.contains 's' then Prototype.replace (Prototype.squareRules (mode.contains 'c') (mode.contains 'v')) p else p
    let p := if mode.contains 't' then Prototype.replace
      ([3,4,16,32,48].map fun n =>
        (selectWindow n (contextBytes n) (slot n 7), Prototype.wordSelect n (contextBytes n) (slot n 7))) p else p
    let p := if mode.contains 'r' then Prototype.rows ((args[1]?).getD "4" |>.toNat!) p else p
    let lines := VG.X86.printer.function p
    let calls := lines.filterMap fun l => match l with | .call n => some n | _ => none
    let assembly := String.intercalate "\n" (lines.map fun l => match l with
      | .text s => s | .call n => "call {" ++ n ++ "}" | .sym .. => "UNSUPPORTED_SYMBOL")
    Lean.Json.mkObj [("name", Lean.toJson name), ("assembly", Lean.toJson (assembly ++ "\n.p2align 6")),
      ("calls", Lean.toJson calls.eraseDups)]
  IO.println (Lean.Json.arr json.toArray).compress
