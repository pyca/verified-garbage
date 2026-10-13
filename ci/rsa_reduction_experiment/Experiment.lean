import VerifiedGarbage.Artifacts.Rsa.AArch64
import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.Rust

/- Private, unproved scheduling experiments. No Artifact or Verified claims. -/
namespace Experiment
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open BlockedRedc

def replaceList (needle replacement xs : List Instr) : List Instr :=
 match xs with
 | [] => []
 | x :: rest => if xs.take needle.length == needle then replacement ++ xs.drop needle.length
                else x :: replaceList needle replacement rest

def high (pipeline : Bool) (nextCoef : Instr) : List Instr :=
 highChain.take 8 ++ (if pipeline then [nextCoef] else []) ++ highChain.drop 8

def tailStep (cache pipeline : Bool) (i : Nat) : List Instr :=
 let lows := if cache then
   replaceList (product true 0 .x13) [.umulh .x13 .x27 .x15]
     (replaceList (product false 0 .x13) [.mul .x .x13 .x27 .x15] lowChain)
   else lowChain
 ([.adc .x .x1 .x7 .x7] : List Instr) ++
 (if pipeline && i > 0 then [] else [ld .x27 .x8 (8*i)]) ++ lows ++
 [.adc .x .x1 .x1 .x7, st .x19 .x16, next .x16] ++
 high (pipeline && i < 7) (ld .x27 .x8 (8*(i+1)))

def cancelStep (pipeline : Bool) (i : Nat) : List Instr :=
 (if pipeline && i > 0 then [] else [.mul .x .x27 .x19 .x15]) ++
 ([st .x27 .x8 (8*i), movi .x1 0] : List Instr) ++ cancelLowChain ++
 [.adc .x .x1 .x1 .x7] ++ high (pipeline && i < 7) (.mul .x .x27 .x19 .x15)

def transformBlock (cache pipeline raw : Bool) (xs : List Instr) : List Instr :=
 let isReduction := (xs.take 1 == (addMemory false).take 1)
 let tails := (if cache then [.vop (.ins .d2 .v28 0 .x15), ld .x15 .x17] else []) ++
     (List.range 8).flatMap (tailStep cache pipeline) ++
     (if cache then [.umov .x .x15 .v28 0] else [])
 let xs := if raw || isReduction then replaceList ((List.range 8).flatMap tail) tails xs else xs
 if pipeline then replaceList ((List.range 8).flatMap cancel)
     ((List.range 8).flatMap (cancelStep true)) xs else xs

def cacheProduct (xs : List Instr) : List Instr :=
 replaceList (product true 0 .x13) [.umulh .x13 .x27 .x12]
  (replaceList (product false 0 .x13) [.mul .x .x13 .x27 .x12] xs)

def cacheStep (xs : List Instr) : List Instr :=
 -- Replace every matching product, not just the first coefficient's.
 match xs with
 | [] => []
 | [x] => [x]
 | x :: y :: rest =>
   if xs.take 2 == product true 0 .x13 then
     [.umulh .x13 .x27 .x12] ++ cacheStep rest
   else if xs.take 2 == product false 0 .x13 then
     [.mul .x .x13 .x27 .x12] ++ cacheStep rest
   else x :: cacheStep (y :: rest)

def outerCacheBlock (xs : List Instr) : List Instr :=
 if xs.take asLoad.length == asLoad then
   [.vop (.ins .d2 .v28 0 .x12)] ++
   replaceList nsLoad (nsLoad ++ [ld .x12 .x17]) (cacheStep xs)
 else if xs.take (addMemory false).length == addMemory false then
   replaceList nsLoad (nsLoad ++ [ld .x12 .x17]) (cacheStep xs)
 else if xs.take (addMemory true).length == addMemory true then
  replaceList ([.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1] : List Instr)
   [.umov .x .x12 .v28 0, .addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1] xs
 else xs

def outerCache : Prog isa → Prog isa
 | .block xs => .block (outerCacheBlock xs)
 | .seq a b => .seq (outerCache a) (outerCache b)
 | .ite c a b => .ite c (outerCache a) (outerCache b)
 | .loop b c => .loop (outerCache b) c
 | .call n b => .call n (outerCache b)
 | .frame a b c => .frame a (outerCache b) c

def transform (cache pipeline raw : Bool) : Prog isa → Prog isa
 | .block xs => .block (transformBlock cache pipeline raw xs)
 | .seq a b => .seq (transform cache pipeline raw a) (transform cache pipeline raw b)
 | .ite c a b => .ite c (transform cache pipeline raw a) (transform cache pipeline raw b)
 | .loop b c => .loop (transform cache pipeline raw b) c
 | .call n b => .call n (transform cache pipeline raw b)
 | .frame a b c => .frame a (transform cache pipeline raw b) c

def diagonalStep (i : Nat) : List Instr :=
 [ld .x1 .x11 (8*i), .mul .x .x2 .x1 .x1, .umulh .x1 .x1 .x1,
  ld .x3 .x16 (16*i), ld .x4 .x16 (16*i+8),
  .extr .x .x6 .x4 .x3 63, .extr .x .x3 .x3 .x5 63,
  mov .x5 .x4, .adcs .x .x3 .x3 .x2, .adcs .x .x6 .x6 .x1,
  st .x3 .x16 (16*i), st .x6 .x16 (16*i+8)]

def diagonal : Prog isa :=
 .seq (.block [mov .x16 .x8, mov .x11 .x9, .lsr .x .x14 .x12 2, .adds .x .x5 .x7 .x7])
 (.seq (countLoop .x14 ((List.range 4).flatMap diagonalStep ++
   [.addImm .x .x16 .x16 64, .addImm .x .x11 .x11 32]))
  (.block [.lsr .x .x5 .x5 63, .adc .x .x5 .x5 .x7, st .x5 .x16]))

def diagonalTransform : Prog isa → Prog isa
 | .seq (.block xs) b =>
   if xs == [mov .x16 .x8, mov .x11 .x9, .lsr .x .x14 .x12 2, movi .x5 0]
   then diagonal else .seq (.block xs) (diagonalTransform b)
 | .seq a b => .seq (diagonalTransform a) (diagonalTransform b)
 | .ite c a b => .ite c (diagonalTransform a) (diagonalTransform b)
 | .loop b c => .loop (diagonalTransform b) c
 | .call n b => .call n (diagonalTransform b)
 | .frame a b c => .frame a (diagonalTransform b) c
 | .block xs => .block xs

def render (name sig : String) (body : Prog isa) : String :=
 let lines := printer.function body ++ printer.funcAlign.map Line.text
 let callees := VG.Rust.dedup (lines.filterMap fun | .call n => some n | _ => none)
 "#[unsafe(naked)]\n" ++ s!"pub(crate) unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
 "    core::arch::naked_asm!(\n" ++ String.join (lines.map (VG.Rust.line printer.call)) ++
 String.join (callees.map fun n => s!"        {n} = sym super::rsa::{n},\n") ++ "    )\n}\n"
end Experiment

def main (args : List String) : IO Unit := do
 let mode := args.head!
 let cache := mode.contains 'c'
 let pipeline := mode.contains 'p'
 let raw := mode.contains 'r'
 let mut source ← IO.FS.readFile "/tmp/vg-rsa-reduction/original.rs"
 let bodies : List (String × VG.Sig × VG.Prog VG.AArch64.isa) :=
   [("vg_rsa_square_4_4", (VG.Spec.Rsa.MontSquare.squareApi .r2).sig,
      (VG.Artifacts.Rsa.AArch64.squareHelper .r2).code),
    ("vg_rsa_square_6_6", (VG.Spec.Rsa.MontSquare.squareApi .y).sig,
      (VG.Artifacts.Rsa.AArch64.squareHelper .y).code),
    ((VG.Spec.Rsa.MontWindow.windowApi).name, (VG.Spec.Rsa.MontWindow.windowApi).sig,
      VG.Artifacts.Rsa.AArch64.windowHelper.code)]
 for (name, sig, body) in bodies do
   let marker := "#[unsafe(naked)]\npub(crate) unsafe extern \"C\" fn " ++ name ++ "("
   let parts := source.splitOn marker
   if parts.length != 2 then throw (IO.userError s!"bad marker {name}")
   let rest := parts[1]!.splitOn "\n}"
   let code := if mode == "diag" then Experiment.diagonalTransform body else if mode == "outer" then Experiment.outerCache body else Experiment.transform cache pipeline raw body
   source := parts[0]! ++ Experiment.render name sig.rust code ++
      "\n}".intercalate rest.tail! |>.replace "}\n\n\n" "}\n\n"
 IO.FS.writeFile s!"/tmp/vg-rsa-reduction/{mode}.rs" source

 for (o,a,b) in [(6,6,6),(1,6,6),(0,6,6),(6,1,5),(1,1,5),(5,1,5)] do
   let code := if a == b || o == 0 then VG.Impl.Bignum.AArch64.SquareEightDispatch.mm o a b
     else VG.Impl.Bignum.AArch64.ProductDispatch.mm o a b
   IO.FS.writeFile s!"/tmp/vg-rsa-reduction/kernel-{mode}-{o}-{a}-{b}.rs"
     (Experiment.render "kernel" "(ws: *mut u64)" (if mode == "diag" then Experiment.diagonalTransform code else if mode == "outer" then Experiment.outerCache code else Experiment.transform cache pipeline raw code))
