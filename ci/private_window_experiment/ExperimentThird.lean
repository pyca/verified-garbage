import VerifiedGarbage.Artifacts.Rsa.AArch64
import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.Rust

/-! Private unproved experiments, emitted by Lean. No Verified claims. -/
namespace Experiment
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def vecs : List VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v27,.v28,.v29,.v30]
def save : List Instr := (BlockedRedc.saved.zip vecs).map fun (r,v) => .vop (.ins .d2 v 0 r)
def restore : List Instr := (BlockedRedc.saved.zip vecs).map fun (r,v) => .umov .x r v 0

def start (a : Nat) (trim : Bool) : List Instr :=
 if trim then [ldh .x8 (sArr Public.aAcc), .addImm .x .x8 .x8 16, ldh .x12 sW, movi .x7 0]
 else Square.squareSetup a

def finishSquare (a : Nat) (trim : Bool) : List Instr :=
 if trim then [ldh .x8 (sArr Public.aAcc), .addImm .x .x8 .x8 16, ldh .x9 (sArr a), ldh .x12 sW]
 else Square.squareSetup a

def squareRows (a : Nat) (holes : Bool) : Prog isa :=
 if holes then
 .loop (.seq (.block (ProductEight.outputPtr true a ++ [st .x7 .x16, st .x7 .x16 120] ++
   SquareEight.code ++ [movi .x10 0] ++ ProductEight.outputPtr false a ++
   [ldh .x15 sW, .lsr .x .x15 .x15 3, .sub .x .x15 .x15 .x12]))
   (.seq (.ite (.nonzero .x .x15) (countLoop .x15 ProductEight.offBlock) (.block []))
     (.block (SquareEightRaw.rowTail a)))) (.nonzero .x .x12)
 else SquareEightRaw.rows a

def rawSquare (a : Nat) (trim holes : Bool) : Prog isa :=
 .seq (.block (start a trim))
 (.seq (if holes then .block [.lsl .x .x14 .x12 4, .add .x .x16 .x8 .x14, st .x7 .x16, st .x7 .x16 8] else WideLoops.zero)
 (.seq (.block [ldh .x8 (sArr a), .lsr .x .x12 .x12 3])
 (.seq (squareRows a holes) (.seq (.block (finishSquare a trim)) WideLoops.diagonal))))

def rawProduct (a b : Nat) (trim : Bool) : Prog isa :=
 .seq (.block (start a trim))
 (.seq WideLoops.zero
 (.seq (.block [ldh .x8 (sArr a), .lsr .x .x12 .x12 3])
 (.seq (ProductEight.rows a b) (.block (if trim then
  [ldh .x8 (sArr Public.aAcc), .addImm .x .x8 .x8 16, ldh .x12 sW] else Square.squareSetup a)))))

def lazyWord (i : Nat) : List Instr :=
 [ld .x3 .x16 (8*i), ld .x4 .x17 (8*i), .logic .and .x .x4 .x4 .x15,
  .sbcs .x .x3 .x3 .x4, st .x3 .x5 (8*i)]
def lazyFinish : Prog isa :=
 .seq (.block [mov .x16 .x8, mov .x17 .x10,
  .lsl .x .x14 .x12 3, .add .x .x14 .x8 .x14, ld .x15 .x14,
  .sub .x .x15 .x7 .x15, .lsr .x .x14 .x12 3, .subs .x .x3 .x7 .x7])
 (countLoop .x14 ((List.range 8).flatMap lazyWord ++
  [.addImm .x .x16 .x16 64, .addImm .x .x17 .x17 64, .addImm .x .x5 .x5 64]))

def reduce (o : Nat) (lazy : Bool) : Prog isa :=
 .seq BlockedRedc.redc (.seq (.block (Square.finishBases o)) (if lazy then lazyFinish else FastFinish.code))

def fast (lazy trim holes : Bool) : Prog isa :=
 let bit := VG.Impl.Bignum.Crt.sBit
 let square := .seq (rawSquare 6 trim holes) (reduce 6 lazy)
 .seq (.block (save ++ [movi .x3 5, sth .x3 bit]))
 (.seq (.loop (.seq square (.block [ldh .x3 bit, .subImm .x .x3 .x3 1, sth .x3 bit])) (.nonzero .x .x3))
 (.seq (VG.Impl.Rsa.AArch64.WindowSelectVector.blocked 32)
 (.seq (rawProduct 6 5 trim)
 (.seq (reduce 6 false) (.block (restore ++ VG.Impl.Rsa.AArch64.WindowFive.resetWindow))))))

def code (lazy trim holes : Bool) : Prog isa :=
 let fallback := VG.Impl.Rsa.AArch64.WindowFive.windowBody
   VG.Proof.Bignum.AArch64.Mont.productEight.mm VG.Proof.Bignum.AArch64.WindowVector.selector.code
 .seq (.block [ldh .x12 sW, .lsr .x .x3 .x12 4, movi .x4 7, .logic .and .x .x4 .x12 .x4])
 (.ite (.nonzero .x .x3) (.ite (.zero .x .x4) (fast lazy trim holes) fallback) fallback)
end Experiment

def main (args : List String) : IO Unit := do
 let mode := args.head!
 let source ← IO.FS.readFile "/tmp/vg-rsa-window-production/src/asm/aarch64/rsa.rs"
 let a := VG.Artifacts.Rsa.AArch64.windowHelper
 let marker := "#[unsafe(naked)]\npub(crate) unsafe extern \"C\" fn " ++ a.name ++ "("
 let parts := source.splitOn marker
 if parts.length != 2 then throw (IO.userError "bad marker")
 let rest := parts[1]!.splitOn "\n}"
 let signature := (rest[0]!.splitOn "{\n")[0]!
 let lines := VG.AArch64.printer.function (Experiment.code (mode != "fused") true true) ++ VG.AArch64.printer.funcAlign.map VG.Line.text
 let callees := VG.Rust.dedup (lines.filterMap fun | .call n => some n | _ => none)
 let result := parts[0]! ++ marker ++ signature ++ "{\n    core::arch::naked_asm!(\n" ++
 String.join (lines.map (VG.Rust.line VG.AArch64.printer.call)) ++
 String.join (callees.map fun n => s!"        {n} = sym super::rsa::{n},\n") ++
 "    )\n}" ++ "\n}".intercalate rest.tail!
 IO.FS.writeFile s!"/tmp/vg-private-next/{mode}.rs" result
