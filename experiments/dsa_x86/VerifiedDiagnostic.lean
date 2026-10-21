import VerifiedGarbage.Impl.Dsa.X86.CombKey
import VerifiedGarbage.TCB.X86.Print
import Lean

open VG VG.X86

/-! Diagnostic programs only: render with the verified implementation checkout's Lean environment.
No Artifact or Verified claim is made for the modified candidates. -/
namespace Diagnostic
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def seq (xs : List (Prog isa)) : Prog isa := xs.foldr .seq (.block [])
def imm (n : Nat) : Src := .imm (BitVec.ofNat 32 n)
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

def fastSeed (n : Nat) : Prog isa := Id.run do
  let mut p := contextSeed n (65*n)
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


def alias (s : String) : String :=
  (s.replace "vg_dsa_comb_prepare_" "proto_dsa_comb_build_").replace
    "vg_dsa_comb_pow_" "proto_dsa_comb_power_"
end Diagnostic

def main (args : List String) : IO Unit := do
  let qfast := args.contains "qfast"
  let pairs := [(16,5),(32,5),(32,7),(32,8),(48,8)]
  let fs := [("vg_dsa_generate_key", VG.Impl.Dsa.X86.Comb.generateKey)] ++
    pairs.flatMap (fun (n,e) => [true,false].map fun prepare =>
      (VG.Impl.Dsa.X86.Comb.name prepare n e, VG.Impl.Dsa.X86.Comb.body prepare n e))
  let json := fs.map fun (name, p) =>
    let p := if qfast then Diagnostic.replace ([3,4].map fun n =>
      (VG.Impl.Mont.X86.Dynamic.contextSetup n,
        .seq (Diagnostic.fastSeed n) (VG.Impl.Mont.X86.Dynamic.setupSquares n))) p else p
    let lines := VG.X86.printer.function p
    let calls := lines.filterMap fun l => match l with | .call n => some (Diagnostic.alias n) | _ => none
    let assembly := String.intercalate "\n" (lines.map fun l => match l with
      | .text s => s | .call n => "call {" ++ Diagnostic.alias n ++ "}" | .sym .. => "UNSUPPORTED_SYMBOL")
    Lean.Json.mkObj [("name", Lean.toJson (Diagnostic.alias name)),
      ("assembly", Lean.toJson (assembly ++ "\n.p2align 6")), ("calls", Lean.toJson calls.eraseDups)]
  IO.println (Lean.Json.arr json.toArray).compress
