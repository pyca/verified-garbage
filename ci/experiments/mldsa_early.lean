-- UNPROVED PERFORMANCE EXPERIMENT. No artifacts or verification claims are constructed.
import VerifiedGarbage.Generic.Keccak.AArch64.MlDsaSign
import VerifiedGarbage.Variants.Keccak.AArch64.Scalar
import VerifiedGarbage.Variants.Keccak.AArch64.Sha3
import VerifiedGarbage.TCB.Rust

open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG.Impl.MlDsa.AArch64.Call

def earlyChecks (p : Params) : Prog isa :=
  .seq (callAt "vg_mldsa_ntt_positive" VG.Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt [(.x0,.ptr cP)]) <|
  .seq (.block (([.movz .x .x24 1 0] : List Instr)++setQ (sc oONES) 0)) <|
  .seq (zPairedVector p) <|
  .seq (ifOk (.seq (pairedLowPhase p) (ifOk (.seq (hintPairedVector p) (.block (onesOk p))))))
    (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p)))

def candidate (v : Proof.Sha3.AArch64.Permutation) (p : Params) : Prog isa :=
  if v.callee.pairedSha3 && p.ℓ != 4 then
    Cached.signWith v.callee (Proof.MlDsa.AArch64.Sign.primsWith v.callee) p (earlyChecks p)
  else Optimized.signWith v.callee (Proof.MlDsa.AArch64.Sign.primsWith v.callee) p (earlyChecks p)

def moduleOf (n : String) : String :=
  if n.startsWith "vg_keccak" then "sha3" else "mldsa"

def main (_args : List String) : IO Unit := do
  for (p, tag) in [(mlDsa44,"44"),(mlDsa65,"65"),(mlDsa87,"87")] do
    let src ← IO.FS.readFile s!"../src/asm/aarch64/mldsa{tag}.rs"
    let mut text := src
    for v in [Variants.Keccak.AArch64.Scalar.variant, Variants.Keccak.AArch64.Sha3.variant] do
      let arts := Generic.Keccak.AArch64.MlDsaSign.artifacts v
      let some a := arts.find? (fun a => a.name == s!"vg_mldsa{tag}_sign{v.callee.suffix}") | throw <| IO.userError "Missing artifact"
      let old := Rust.function a moduleOf
      let new := Rust.function.functionOf a (target.printer.function (candidate v p)) moduleOf
      unless (text.splitOn old).length == 2 do
        IO.FS.writeFile s!"../../mldsa-experiments/expected-{a.name}.txt" old
        throw <| IO.userError s!"Could not find exactly one function {a.name}"
      text := text.replace old new
    IO.FS.writeFile s!"../../mldsa-experiments/mldsa{tag}.rs" text
