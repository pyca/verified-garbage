-- UNPROVED experiment. All instructions and Rust templates use the existing Lean printer.
-- No Artifact or verification claim is constructed for the candidate.
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedLoop
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedRest
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecks
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst
import VerifiedGarbage.Variants.Keccak.AArch64.Scalar
import VerifiedGarbage.Variants.Keccak.AArch64.Sha3
import VerifiedGarbage.TCB.Rust
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG.Impl.MlDsa.AArch64.Call
namespace ChecksPrototype

def phase (p : Params) (z pair : Bool) : Prog isa :=
  let n := if z then p.ℓ else p.k
  let one := if z then zR p else r0R p
  let two := if z then zPair p else r0Pair p
  if pair then .seq (seqOk (fun j => two (2*j)) 0 (n/2))
    (if n%2=1 then ifOk (one (n-1)) else .block [])
  else seqOk one 0 n

def checks (p : Params) (zp rp : Bool) (swap : Bool := false) : Prog isa :=
  .seq (.seq (callAt "vg_mldsa_ntt_positive" VG.Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
      [(.x0,.ptr cP)])
    (.seq (.block (([.movz .x .x24 1 0] : List Instr)++setQ (sc oONES) 0)) (phase p (!swap) (if swap then rp else zp))))
    (ifOkElse
      (.seq (phase p swap (if swap then zp else rp))
        (ifOkElse
          (.seq (hintPairedVector p)
            (.seq (.block (onesOk p))
              (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p)))))
          (.block (kapAdd p))))
      (.block (kapAdd p)))

def program (c : Impl.Sha3.AArch64.Callee) (p : Params) (ch : Prog isa) : Prog isa :=
  if c.pairedSha3 && p.k != 4 then
    Cached.signWith c (Proof.MlDsa.AArch64.Sign.primsWith c) p ch
  else Optimized.signWith c (Proof.MlDsa.AArch64.Sign.primsWith c) p ch

-- Preserve the original function's signature/metadata; emit every instruction,
-- label, call and symbol reference from the modeled program using Rust.template.
def function (old : String) (c : Impl.Sha3.AArch64.Callee) (p : Params) (ch : Prog isa) : IO String := do
  let P := target.printer
  let fs := if c.pairedSha3 then ["sha3"] else []
  let ls := (fs.flatMap P.enableFeature).map Line.text ++ P.function (program c p ch) ++
    (fs.flatMap P.disableFeature).map Line.text ++ P.funcAlign.map Line.text
  let calls := Rust.dedup (ls.filterMap fun | .call n => some n | _ => none)
  let syms := Rust.dedup (ls.filterMap fun | .sym _ _ n => some n | _ => none)
  let mut bindings := ""
  for n in calls ++ syms do
    let some l := (old.splitOn "\n").find? (fun l => (l.splitOn (n ++ " = sym ")).length == 2)
      | if n == "vg_mldsa_fused_pair_z" || n == "vg_mldsa_fused_pair_r0" then
          bindings := bindings ++ s!"        {n} = sym super::mldsa::{n},\n"
          continue
        else throw <| IO.userError s!"Unknown binding {n}"
    bindings := bindings ++ l ++ "\n"
  let hdr := (old.splitOn "    core::arch::naked_asm!(").head!
  return hdr ++ "    core::arch::naked_asm!(\n" ++ Rust.template P.call ls ++ bindings ++ "    )\n}\n"

def main (args : List String) : IO Unit := do
  let mode := args.headD "both"
  for (tag,p) in [("44",mlDsa44),("65",mlDsa65),("87",mlDsa87)] do
    let path := s!"../src/asm/aarch64/mldsa{tag}.rs"
    let mut src ← IO.FS.readFile path
    for c in [Variants.Keccak.AArch64.Scalar.variant.callee, Variants.Keccak.AArch64.Sha3.variant.callee] do
      let name := s!"vg_mldsa{tag}_sign{c.suffix}"
      let marker := s!"pub(crate) unsafe extern \"C\" fn {name}("
      let [pre,rest] := src.splitOn marker | throw <| IO.userError s!"Missing {name}"
      let old := marker ++ ((rest.splitOn "\n}\n").head!) ++ "\n}\n"
      let unchanged ← function old c p (pairedChecks p)
      unless old == unchanged do
        IO.FS.writeFile s!"../../mldsa3791-experiments/expected-{name}.rs" unchanged
        IO.FS.writeFile s!"../../mldsa3791-experiments/actual-{name}.rs" old
        throw <| IO.userError s!"Baseline emission mismatch for {name}"
      let ch := if mode == "baseline" then pairedChecks p else checks p (mode == "z" || mode == "both") (mode == "r0" || mode == "both") (mode == "swap")
      let new ← function old c p ch
      src := pre ++ new ++ "\n}\n".intercalate ((rest.splitOn "\n}\n").drop 1)
    IO.FS.writeFile s!"../../mldsa3791-experiments/{mode}-mldsa{tag}.rs" src
end ChecksPrototype

def main := ChecksPrototype.main
