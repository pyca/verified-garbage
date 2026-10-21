import VerifiedGarbage.Impl.Dsa.X86.GenerateKey
import VerifiedGarbage.Impl.Dsa.X86.Generate
import VerifiedGarbage.Impl.Dsa.X86.Generation.Entry
import VerifiedGarbage.Impl.Mont.X86.Window
import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Spec.Rsa.FixedBaseComb
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
def stackPower (n _e : Nat) (power : Prog isa) (entries : Nat := 16) : Prog isa :=
  let bytes := contextBytes n + 8 * entries * n
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

/-- Wider fixed windows for long public prime-search exponents only. -/
def wideWindow (n e bits : Nat) : Prog isa :=
  let tab := contextBytes n
  let count := 2^bits
  let product := mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 6) (slot n 7)
  let step := seq [
    mul (contextMod n) 0 (slot n 2) (slot n 7) (slot n 7) (slot n 5),
    copyOut (2*n) (slot n 7),
    .block [.mov .edx (.reg .edi), .alu .add .edx (imm (entry n tab count)),
      .alu .cmp .esi (.reg .edx)]]
  let table := seq [copyWords n (slot n 6) (entry n tab 0),
    copyWords n (slot n 5) (entry n tab 1), copyWords n (slot n 5) (slot n 7),
    .block [.mov .esi (.reg .edi), .alu .add .esi (imm (entry n tab 2))], .loop step .ne]
  let body := fun k => seq [
    seq (List.replicate k (square n)),
    .block [.mov .eax (.mem (sc (slot n 8+4*(e-1)))), .shift .shr .eax (32-k),
      .store (sc windowOffset) .eax],
    .seq (.block [.mov .ecx (imm 0)]) (wordLoop e ([
      .mov .eax (.mem (at_ .ebp (slot n 8))), .mov .ebx (.reg .eax), .shift .shr .ebx (32-k)] ++
      List.replicate k (.alu .add .eax (.reg .eax)) ++ [
      .alu .add .eax (.reg .ecx), .store (at_ .ebp (slot n 8)) .eax, .mov .ecx (.reg .ebx)])),
    publicSelect n tab (slot n 7), product]
  stackPower n e (seq [
    mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 4) (slot n 3),
    mul (contextMod n) 0 (slot n 2) (slot n 5) (slot n 5) (slot n 4), table,
    (if 32*e % bits == 0 then .block [] else body (32*e % bits)),
    .block [.mov .esi (imm (32*e/bits))],
    .loop (.seq (body bits) (.block [.alu .sub .esi (imm 1), .alu .cmp .esi (imm 0)])) .ne,
    mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 6) (slot n 3)]) count

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

/-- Small inner-loop chunks for the triangular product, with a public
prefix handling the row length modulo the chunk size. -/
def tiledCross (n acc a chunk : Nat) : Prog isa :=
  let N := 2*n
  let tile := fun k => .block ((List.range k).flatMap (fun j => [
    .mov .eax (.mem (at_ .ecx (a+4*j))), .mul .esi,
    .alu .add .eax (.mem (at_ .ebp (acc+4*j))), .alu .adc .edx (imm 0),
    .alu .add .eax (.reg .ebx), .alu .adc .edx (imm 0),
    .store (at_ .ebp (acc+4*j)) .eax, .mov .ebx (.reg .edx)]) ++
    [.alu .add .ecx (imm (4*k)), .alu .add .ebp (imm (4*k))])
  let headWords :=  .seq (.block [.alu .cmp .eax (imm 0)]) (.ite .ne (seq [
    .block [.alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .eax (.reg .ecx), .store (at_ .esp 4) .eax],
    .loop (.seq (tile 1) (.block [.alu .cmp .ecx (.mem (at_ .esp 4))])) .ne]) (.block []))
  let check := .block [.mov .eax (.reg .edi), .alu .add .eax (imm (4*N)), .alu .cmp .ecx (.reg .eax)]
  .frame (.alloc 8) (seq [
    .block [.mov .eax (imm 0), .store (at_ .esp 0) .eax],
    .loop (seq [
      .block [.mov .eax (.mem (at_ .esp 0)), .mov .ecx (.reg .edi), .alu .add .ecx (.reg .eax),
        .mov .esi (.mem (at_ .ecx a)), .alu .add .ecx (imm 4), .mov .ebp (.reg .ecx),
        .alu .add .ebp (.reg .eax), .mov .ebx (imm 0),
        .mov .edx (.reg .eax), .shift .shr .edx 2, .mov .eax (imm (N-1)),
        .alu .sub .eax (.reg .edx), .alu .and .eax (imm (chunk-1))],
      headWords, check, .ite .ne (.loop (.seq (tile chunk) check) .ne) (.block []),
      .block [.store (at_ .ebp acc) .ebx, .mov .eax (.mem (at_ .esp 0)), .alu .add .eax (imm 4),
        .store (at_ .esp 0) .eax, .alu .cmp .eax (imm (4*(N-1)))]]) .ne]) (.free 8)

/-- A triangular raw product, doubled, plus the diagonal, followed by the
existing Montgomery reduction rows. This is an unproven square experiment. -/
def fastSquare (compact deferred : Bool) (crossChunk n o a : Nat) : Prog isa :=
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
      .alu .add .eax (.mem (sc 24)), .alu .adc .edx (imm 0),
      .store (at_ .ebp acc) .eax, .store (sc 24) .edx,
      .alu .sub .ebp (imm (4*N))]]
  let red := seq [
    .block [.mov .eax (imm 0), .store (sc 24) .eax, .mov .ebp (.reg .edi)],
    .loop (seq [.block (redDigit acc 0 (slot n 1)),
      (if deferred then deferredRow else fullRow),
      .block [.alu .add .ebp (imm 4), .mov .edx (.reg .edi),
        .alu .add .edx (imm (4*N)), .alu .cmp .ebp (.reg .edx)]]) .ne,
    (if deferred then .block [.mov .eax (.mem (sc 24)), .store (sc (acc+8*N)) .eax] else .block []),
    csubW (contextMod n) (acc+4*N) o]
  .frame (.push [.esi]) (seq ([zerosW acc (2*N+1)] ++ (if compact then [if crossChunk > 1 then tiledCross n acc a crossChunk else compactCross] else cross) ++
    [chainW .adc (2*N) acc acc acc, diagonal, red])) (.pop .esi 1)

/-- Fixed-address masked table scan, accumulating each output word in a
register. Masks are computed once per window, without secret indexing. -/
def wordSelectBody (n tab dst entries : Nat) (mask : Nat → MemOp) : Prog isa :=
  seq [
    .block ((List.range entries).flatMap fun j => windowMask j ++ [.store (mask j) .ecx]),
    .block [.mov .ebp (.reg .edi)],
    .loop (.block ([.mov .ebx (imm 0)] ++ (List.range entries).flatMap (fun j => [
      .mov .eax (.mem (at_ .ebp (entry n tab j))), .alu .and .eax (.mem (mask j)),
      .alu .or .ebx (.reg .eax)]) ++ [
      .store (at_ .ebp dst) .ebx, .alu .add .ebp (imm 4),
      .mov .eax (.reg .edi), .alu .add .eax (imm (8*n)), .alu .cmp .ebp (.reg .eax)])) .ne]

def wordSelect (n tab dst : Nat) (entries : Nat := 16) : Prog isa :=
  .frame (.alloc (4*entries))
    (wordSelectBody n tab dst entries (fun j => at_ .esp (4*j))) (.free (4*entries))

def workspaceSelect (n tab dst : Nat) : Prog isa :=
  wordSelectBody n tab dst 32 (fun j => sc (slot n 1+4*j))

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

def squareRules (compact deferred : Bool) (crossChunk : Nat) : List (Prog isa × Prog isa) :=
  [3,4,16,32,48].flatMap fun n => [4,5,6].map fun i =>
    (mul (contextMod n) 0 (slot n 2) (slot n i) (slot n i) (slot n i),
      fastSquare compact deferred crossChunk n (slot n i) (slot n i))

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

/-- Persistent key-generation comb storage, disjoint from the DSA fields
and scalar suffix and inside the existing minimum scratch allocation. -/
def combBase (n : Nat) : Nat := if n == 16 then 9216 else 16384
def combTable (n : Nat) : Nat := combBase n + 16*n

def copyToComb (n src : Nat) : Prog isa := seq [
  .block [.mov .eax (.reg .esi), .mov .edx (imm (8*n)), .mul .edx,
    .alu .add .eax (.reg .edi), .alu .add .eax (imm (combTable n)),
    .mov .ecx (.reg .eax), .mov .ebp (.reg .edi), .mov .ebx (imm (2*n))],
  .loop (.block [.mov .eax (.mem (at_ .ebp src)), .store (at_ .ecx 0) .eax,
    .alu .add .ecx (imm 4), .alu .add .ebp (imm 4), .alu .sub .ebx (imm 1)]) .ne]

def combBuild (n e : Nat) : Prog isa :=
  let d := VG.Spec.Rsa.FixedBaseComb.rows (32*e)
  let tab := combTable n
  seq [copyWords n (slot n 0) (combBase n), copyWords n (slot n 4) (combBase n+8*n),
    mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 4) (slot n 3),
    mul (contextMod n) 0 (slot n 2) (slot n 5) (slot n 5) (slot n 4),
    copyWords n (slot n 6) tab, copyWords n (slot n 5) (entry n tab 1),
    .block [.mov .eax (imm 1), .store (sc 28) .eax],
    .loop (seq [
      .block [.mov .esi (imm d)],
      .loop (.seq (mul (contextMod n) 0 (slot n 2) (slot n 5) (slot n 5) (slot n 5))
        (.block [.alu .sub .esi (imm 1), .alu .cmp .esi (imm 0)])) .ne,
      .block [.mov .esi (.mem (sc 28)), .alu .add .esi (.reg .esi), .store (sc 28) .esi],
      copyToComb n (slot n 5), .block [.alu .cmp .esi (imm 16)]]) .ne,
    .block [.mov .esi (imm 1)],
    .loop (seq [
      .block [.mov .eax (imm 0), .alu .sub .eax (.reg .esi), .alu .and .eax (.reg .esi),
        .store (sc 28) .eax, .mov .edx (.reg .esi), .alu .sub .edx (.reg .eax), .store (sc windowOffset) .edx],
      publicSelect n tab (slot n 6),
      .block [.mov .eax (.mem (sc 28)), .store (sc windowOffset) .eax],
      publicSelect n tab (slot n 5),
      mul (contextMod n) 0 (slot n 2) (slot n 7) (slot n 6) (slot n 5),
      copyToComb n (slot n 7), .block [.alu .add .esi (imm 1), .alu .cmp .esi (imm 32)]]) .ne]

def combPower (n e : Nat) (pub : Bool) : Prog isa :=
  let d := VG.Spec.Rsa.FixedBaseComb.rows (32*e)
  let ew := (5*d+31)/32
  let digit := .block ([.mov .ebx (imm 0)] ++ (List.range 5).flatMap (fun j =>
    let bit := (j+1)*d-1
    [.mov .eax (.mem (sc (slot n 8+4*(bit/32))))] ++
    (if bit%32 == 0 then [] else [.shift .shr .eax (bit%32)]) ++
    [.alu .and .eax (imm 1)] ++ List.replicate j (.alu .add .eax (.reg .eax)) ++
    [.alu .or .ebx (.reg .eax)]) ++ [.store (sc windowOffset) .ebx])
  let shiftOne := .seq (.block [.mov .ecx (imm 0)]) (wordLoop ew [
    .mov .eax (.mem (at_ .ebp (slot n 8))), .mov .ebx (.reg .eax), .shift .shr .ebx 31,
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .ecx),
    .store (at_ .ebp (slot n 8)) .eax, .mov .ecx (.reg .ebx)])
  seq [copyWords n (combTable n) (slot n 6),
    (if e < ew then zerosW (slot n 8+4*e) (ew-e) else .block []),
    .block [.mov .esi (imm d)],
    .loop (seq [square n, digit, shiftOne,
      (if pub then publicSelect n (combTable n) (slot n 7) else wordSelect n (combTable n) (slot n 7) 32),
      mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 6) (slot n 7),
      .block [.alu .sub .esi (imm 1), .alu .cmp .esi (imm 0)]]) .ne,
    mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 6) (slot n 3)]

def combName (prepare : Bool) (n e : Nat) : String :=
  (if prepare then "proto_dsa_comb_build_" else "proto_dsa_comb_power_") ++ toString n ++ "_" ++ toString e

def combBody (prepare : Bool) (n e : Nat) : Prog isa := seq [
  .block VG.Impl.Dsa.X86.Pow.save,
  (if prepare then .seq (contextSetup n) (combBuild n e)
    else .seq (.block (setupInverse (slot n 0) 0)) (one n (slot n 3))),
  combPower n e prepare, .block VG.Impl.Dsa.X86.Pow.restore]

def combCall (prepare : Bool) (n e : Nat) : Prog isa :=
  .seq (.block [.mov .eax (imm ((combBase n+34*8*n)/8))])
    (.frame (.push [.eax, .edi]) (.call (combName prepare n e) (combBody prepare n e)) (.pop .eax 2))

def combFunctions (fs : List (String × Prog isa)) : List (String × Prog isa) := Id.run do
  let pairs := [(16,5),(32,5),(32,7),(32,8),(48,8)]
  let check := replace (pairs.map fun (n,e) => (VG.Impl.Dsa.X86.Pow.call n e, combCall true n e))
    VG.Impl.Dsa.X86.Generate.checkParameters
  let derive := replace (pairs.map fun (n,e) => (VG.Impl.Dsa.X86.Pow.call n e, combCall false n e))
    (replace (domains.map fun (p,q) => (VG.Impl.Dsa.X86.Generate.parameters p q, .block []))
      VG.Impl.Dsa.X86.Generate.deriveKey)
  let mut result := fs.filter fun f => f.1 != "vg_dsa_generate_key" && f.1 != "proto_dsa_derive_prevalidated"
  result := result ++ [("proto_dsa_comb_check_parameters", check), ("proto_dsa_comb_derive_key", derive),
    ("vg_dsa_generate_key", VG.Impl.Dsa.X86.GenerateKey.code "proto_dsa_comb_check_parameters"
      "proto_dsa_comb_derive_key" check derive)]
  for (n,e) in pairs do
    for prepare in [true,false] do
      result := result ++ [(combName prepare n e, combBody prepare n e)]
  return result

/-- Reuse RSA's existing runtime-width multiplication helper. Its scratch
range fits in the unused modulus padding plus slots one and two for n>=3. -/
def sharedMul (n o a b : Nat) : Prog isa :=
  let borrow := if n < 5 then 16 else 0
  let start := slot n 1-borrow
  .frame (.alloc (36+borrow)) (seq [
    .block ((List.range (borrow/4)).flatMap fun j =>
      [.mov .eax (.mem (sc (start+4*j))), .store (at_ .esp (36+4*j)) .eax]),
    .block ([.store (at_ .esp 0) .edi] ++
      ([contextBytes n / 8, n, slot n 0, 0, start, o, a, b].zipIdx.flatMap fun (v,i) =>
        [.mov .eax (imm v), .store (at_ .esp (4*(i+1))) .eax])),
    .call "vg_rsa_mont_mul_at" (.block []),
    .block ((List.range (borrow/4)).flatMap fun j =>
      [.mov .eax (.mem (at_ .esp (36+4*j))), .store (sc (start+4*j)) .eax])]) (.free (36+borrow))

def sharedRules : List (Prog isa × Prog isa) :=
  [3,4,16,32,48].flatMap fun n =>
    [(4,4,4),(6,4,3),(5,5,4),(7,7,5),(6,6,6),(6,6,7),(6,6,3),(5,5,5),(7,6,5)].map fun (o,a,b) =>
      (mul (contextMod n) 0 (slot n 2) (slot n o) (slot n a) (slot n b),
        sharedMul n (slot n o) (slot n a) (slot n b))

def abiNamed (callee : String) : Prog isa :=
  let saved := [(Reg.ebx, 0), (.esi, 4), (.ebp, 8), (.edi, 12)]
  let sentinels := [(Reg.ebx, 305419896), (.esi, 591751049), (.ebp, 878082202), (.edi, 1164413355)]
  .frame (.alloc 16) (seq [
    .block (saved.map (fun (r,d) => .store (at_ .esp d) r) ++ [
      .mov .eax (.mem (at_ .esp 20)), .mov .edx (.mem (at_ .esp 24))]),
    .frame (.push [.edx, .eax]) (seq [
      .block (sentinels.map fun (r,v) => .mov r (imm v)),
      .call callee (.block []),
      .block ([.mov .eax (imm 0)] ++ sentinels.flatMap (fun (r,v) =>
        [.alu .xor r (imm v), .alu .or .eax (.reg r)]))]) (.pop .edx 2),
    .block (saved.map fun (r,d) => .mov r (.mem (at_ .esp d)))]) (.free 16)

def abiWrapper (n e : Nat) : Prog isa := abiNamed (VG.Impl.Dsa.X86.Pow.name n e)

end Prototype

def main (args : List String) : IO Unit := do
  let mode := args.head!
  let fs := if mode == "abic" then [(16,5),(32,5),(32,7),(32,8),(48,8)].flatMap (fun (n,e) =>
    [true,false].map fun prepare =>
      let name := Prototype.combName prepare n e
      (name.replace "proto_dsa_" "proto_dsa_abi_", Prototype.abiNamed name)) else if mode == "abi" then Prototype.widths.map (fun (n,e) =>
    ("proto_dsa_abi_pow_" ++ toString n ++ "_" ++ toString e, Prototype.abiWrapper n e)) else Prototype.functions (mode.contains 'd') (mode.contains 'w') (mode.contains 'p')
  let fs := if mode.contains 'm' then Prototype.combFunctions fs else fs
  -- Isolate promotion candidates: ordinary powers, signing, verification and
  -- parameter generation retain their checked baseline bodies.
  let fs := if mode.contains 'k' then fs.filter (fun (name, _) =>
    name == "vg_dsa_generate_key" || name.startsWith "proto_dsa_comb_") else fs
  let json := fs.map fun (name, p) =>
    let p := if mode.contains 'o' then Prototype.replace
      ([16,32,48].map fun n =>
        (Prototype.wordSelect n (Prototype.combTable n) (slot n 7) 32,
          Prototype.workspaceSelect n (Prototype.combTable n) (slot n 7))) p else p
    let p := if mode.contains 'q' then Prototype.replace [(exponentiate 3 6, Prototype.window 3 6 true)] p else p
    let p := if mode.contains 'z' then Prototype.replace
      ([(16,32),(32,64),(48,96)].map fun (n,e) => (Prototype.window n e true, Prototype.wideWindow n e 6)) p else p
    let p := if mode.contains 'f' then Prototype.replace ([3,4,16,32,48].map fun n => (contextSeed n, Prototype.fastSeed n)) p else p
    let p := if mode != "baseline" && mode.contains 's' then Prototype.replace (Prototype.squareRules (mode.contains 'c') (mode.contains 'v') (if mode.contains 'j' then 8 else if mode.contains 'u' then 4 else 1)) p else p
    let p := if mode.contains 't' then Prototype.replace
      ([3,4,16,32,48].map fun n =>
        (selectWindow n (contextBytes n) (slot n 7), Prototype.wordSelect n (contextBytes n) (slot n 7))) p else p
    let p := if mode.contains 'h' then Prototype.replace Prototype.sharedRules p else p
    let p := if mode.contains 'r' then Prototype.rows ((args[1]?).getD "4" |>.toNat!) p else p
    let lines := VG.X86.printer.function p
    let calls := lines.filterMap fun l => match l with | .call n => some n | _ => none
    let assembly := String.intercalate "\n" (lines.map fun l => match l with
      | .text s => s | .call n => "call {" ++ n ++ "}" | .sym .. => "UNSUPPORTED_SYMBOL")
    Lean.Json.mkObj [("name", Lean.toJson name), ("assembly", Lean.toJson (assembly ++ "\n.p2align 6")),
      ("calls", Lean.toJson calls.eraseDups)]
  IO.println (Lean.Json.arr json.toArray).compress
