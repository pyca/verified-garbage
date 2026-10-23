import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
import VerifiedGarbage.Impl.Ed448.AArch64.Verify
import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Resident
import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Resident
import VerifiedGarbage.Impl.Ed448.SignedWindow
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
namespace TrialEd448
open VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot BITS)

def direct : List Instr :=
 [.lsl .x .x8 .x11 7, .lsl .x .x9 .x11 6, .add .x .x8 .x8 .x9, .add .x .x8 .x8 .x3] ++
 (List.range 24).flatMap fun w =>
 [.ldr .x .x4 .x8 (TAB + 8*w), st .x4 (slot (6+w/8)+8*(w%8))]

def window (skip : Bool) : Prog isa :=
 .seq dbl4Loop <| .seq (.block digitOf) <|
 if skip then .ite (.nonzero .x .x11) (.seq (.block direct) Point56.addCall) (.block [])
 else .seq (.block direct) Point56.addCall

def windows (skip : Bool) : Prog isa :=
 .seq nibbles <| .seq (.block kInit) <|
 .loop (.seq (.block [.subImm .x .x19 .x19 1]) (window skip)) (.nonzero .x .x19)

def digitStep (w : Nat) : List Instr :=
 [.add .x .x4 .x4 .x6, .addImm .x .x4 .x4 (2^(w-1)), .movz .x .x8 (2^w-1) 0,
 .logic .and .x .x4 .x4 .x8,
 .subImm .x .x7 .x4 (2^w), .movz .x .x8 (2^(w-1)) 0, .tst .x .x4 .x8,
 .cselc .x .x7 .x4 .x7 .eq,
 .movz .x .x8 1 0, .tst .x .x4 .x8, .movz .x .x9 0 0, .cselc .x .x7 .x9 .x7 .eq,
 .add .x .x6 .x6 .x5, .addImm .x .x6 .x6 (2^(w-1)), .sub .x .x6 .x6 .x7, .lsr .x .x6 .x6 1]

def recodeBody (w : Nat) : List Instr :=
 [.add .x .x2 .x3 .x19, .ldrb .x4 .x2 (BITS+w-1)] ++
 ((List.range (w-1)).reverse.flatMap fun i =>
 [.ldrb .x5 .x2 (BITS+i), .lsl .x .x4 .x4 1, .add .x .x4 .x4 .x5]) ++
 digitStep w ++ [.strb .x7 .x2 BITS, .addImm .x .x19 .x19 1, .subImm .x .x9 .x19 464]

def recodeBits (w : Nat) : Prog isa :=
 .seq (.block ([.movz .x .x4 0 0] ++ (List.range 10).map (fun i => Instr.strb .x4 .x3 (BITS+456+i)) ++
 [.movz .x .x19 0 0, .movz .x .x6 (2^(w-1)) 0])) <|
 .loop (.block (recodeBody w)) (.nonzero .x .x9)

def recode (w : Nat) : Prog isa := .seq (bitsAt .x3 KB 0 BITS) (recodeBits w)

def negate : Prog isa := VG.Impl.X448.AArch64.Fast.opsK
 [.sub (slot 6) (slot 19) (slot 6)]

def sparseAdd (odd : Bool := false) : Prog isa :=
 .seq (.block [.add .x .x2 .x3 .x19, .ldrb .x11 .x2 BITS]) <|
 .ite (.nonzero .x .x11)
  (.seq (.block ([.lsr .x .x21 .x11 7, .movz .x .x9 256 0, .sub .x .x9 .x9 .x11,
    .movz .x .x8 128 0, .tst .x .x11 .x8, .cselc .x .x11 .x9 .x11 .ne] ++ (if odd then [.lsr .x .x11 .x11 1] else []) ++ direct)) <|
   .seq (.ite (.nonzero .x .x21) negate (.block [])) Point56.addCall)
  (.block [])

def sparse (w : Nat) : Prog isa :=
 .seq (recode w) <| .seq (.block
 (VG.Impl.X448.AArch64.Base.constSlot (slot 3) 0 ++ VG.Impl.X448.AArch64.Base.constSlot (slot 4) 1 ++
 VG.Impl.X448.AArch64.Base.constSlot (slot 5) 1 ++ VG.Impl.X448.AArch64.Base.constSlot (slot 19) 0 ++ VG.Impl.X448.AArch64.Base.constSlot (slot 20) 1 ++
 [.movz .x .x19 464 0])) <|
 .loop (.seq (.block [.subImm .x .x19 .x19 1]) <| .seq Point56.doubleCall <|
 .seq sparseAdd (.block [.addImm .x .x9 .x19 0])) (.nonzero .x .x9)

def trimBody : List Instr :=
 [.subImm .x .x19 .x19 1, .add .x .x2 .x3 .x19, .ldrb .x9 .x2 BITS,
  .movz .x .x8 1 0, .subImm .x .x4 .x19 1, .lsr .x .x4 .x4 63,
  .logic .orr .x .x9 .x9 .x4]
def trimmed (w : Nat) (odd : Bool) : Prog isa :=
 .seq (recode w) <| .seq (.block
 (VG.Impl.X448.AArch64.Base.constSlot (slot 3) 0 ++ VG.Impl.X448.AArch64.Base.constSlot (slot 4) 1 ++
 VG.Impl.X448.AArch64.Base.constSlot (slot 5) 1 ++ VG.Impl.X448.AArch64.Base.constSlot (slot 19) 0 ++ VG.Impl.X448.AArch64.Base.constSlot (slot 20) 1 ++
 [.movz .x .x19 464 0])) <|
 .seq (.loop (.block trimBody) (.zero .x .x9)) <|
 .seq (.block [.addImm .x .x19 .x19 1]) <|
 .loop (.seq (.block [.subImm .x .x19 .x19 1]) <| .seq Point56.doubleCall <|
 .seq (sparseAdd odd) (.block [.addImm .x .x9 .x19 0])) (.nonzero .x .x9)

def oddInit : List Instr :=
 VG.Impl.Curve448.AArch64.copy RX (slot 8) ++ VG.Impl.Curve448.AArch64.copy RY (slot 9) ++
 VG.Impl.X448.AArch64.Base.constSlot (slot 19) 0 ++ VG.Impl.X448.AArch64.Base.constSlot (slot 20) 1 ++
 VG.Impl.Curve448.AArch64.copy (slot 3) (slot 6) ++ VG.Impl.Curve448.AArch64.copy (slot 4) (slot 7) ++
 VG.Impl.X448.AArch64.Base.constSlot (slot 5) 1 ++ [.movz .x .x19 0 0] ++ tabStore

def oddBody (n : Nat) : Prog isa :=
 .seq Point56.addCall (.block (tabStore ++ [.addImm .x .x19 .x19 1, .subImm .x .x9 .x19 n]))

def oddTable (w : Nat) : Prog isa :=
 .seq (.block oddInit) <| .seq Point56.doubleCall <|
 .seq (.block (Point56.copy3 6 3 ++
 (List.range 24).flatMap (fun i => [ld .x4 (TAB+8*i),st .x4 (slot (3+i/8)+8*(i%8))]) ++
 [.movz .x .x19 1 0])) <|
 .loop (oddBody (2^(w-2))) (.nonzero .x .x9)

def sdAddress : List Instr :=
 [.add .x .x2 .x3 .x19, .addImm .x .x2 .x2 16,
 .subImm .x .x9 .x19 432, .lsr .x .x9 .x9 63, .addImm .x .x8 .x2 2304,
 .tst .x .x9 .x9, .cselc .x .x2 .x2 .x8 .ne]


def affineFn : Prog isa :=
 .seq (.block ((List.range 8).map (fun i => st (VG.Impl.X448.AArch64.Fast.saved i) (2784+8*i)) ++
 [st .x30 2856, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++
 VG.Impl.X448.AArch64.Base.addAffine (slot 3) (slot 4) (slot 5) (slot 6) (slot 7)))
 (.block ((List.range 8).map (fun i => ld (VG.Impl.X448.AArch64.Fast.saved i) (2784+8*i)) ++ [ld .x30 2856]))

def baseSelect : List Instr :=
 [.adrSym .x8 "VG_ED448_PUBLIC_BASE", .lsl .x .x9 .x11 7, .add .x .x8 .x8 .x9] ++
 (List.range 16).flatMap (fun i => [.ldr .x .x4 .x8 (8*i),st .x4 (slot (6+i/8)+8*(i%8))])

def baseAdd : Prog isa :=
 .seq (.block (sdAddress ++ [.ldrb .x11 .x2 0])) <|
 .ite (.nonzero .x .x11)
  (.seq (.block ([.lsr .x .x21 .x11 7, .movz .x .x9 256 0, .sub .x .x9 .x9 .x11,
    .movz .x .x8 128 0, .tst .x .x11 .x8, .cselc .x .x11 .x9 .x11 .ne] ++ baseSelect)) <|
   .seq (.ite (.nonzero .x .x21) negate (.block [])) (.call "ed448_affine_trial" affineFn))
  (.block [])

def jointStep : Prog isa :=
 .seq (.block [.subImm .x .x19 .x19 1]) <| .seq Point56.doubleCall <|
 .seq baseAdd <| .seq (sparseAdd true) (.block [.addImm .x .x9 .x19 0])

def joint (bw kw : Nat) (trim : Bool) : Prog isa :=
 .seq (recodeBits bw) <|
 .seq (.block ((List.range 464).flatMap (fun i => [.ldrb .x4 .x3 (BITS+i), .strb .x4 .x3 (if i<432 then 16+i else 2320+i)]))) <|
 .seq (recode kw) <|
 .seq (.block (VG.Impl.X448.AArch64.Base.constSlot (slot 3) 0 ++
 VG.Impl.X448.AArch64.Base.constSlot (slot 4) 1 ++ VG.Impl.X448.AArch64.Base.constSlot (slot 5) 1 ++
 VG.Impl.X448.AArch64.Base.constSlot (slot 19) 0 ++ VG.Impl.X448.AArch64.Base.constSlot (slot 20) 1 ++
 [.movz .x .x19 464 0])) <|
 if trim then
  .seq (.loop (.block (trimBody ++ [.addImm .x .x7 .x9 0] ++ sdAddress ++
   [.ldrb .x8 .x2 0, .logic .orr .x .x9 .x7 .x8])) (.zero .x .x9)) <|
  .seq (.block [.addImm .x .x19 .x19 1]) (.loop jointStep (.nonzero .x .x9))
 else .loop jointStep (.nonzero .x .x9)

def jointCross : Prog isa :=
 .seq Point56.doubleCall <| .seq Point56.doubleCall <|
 .seq (.block (Point56.copy3 0 3 ++ VG.Impl.Curve448.AArch64.copy (slot 3) RX ++
 VG.Impl.Curve448.AArch64.copy (slot 4) RY ++ VG.Impl.X448.AArch64.Base.constSlot (slot 5) 1)) <|
 .seq Point56.doubleCall <| .seq Point56.doubleCall <|
 VG.Impl.X448.AArch64.Fast.opsK [.mul (slot 12) (slot 0) (slot 5), .mul (slot 13) (slot 3) (slot 2),
 .mul (slot 14) (slot 1) (slot 5), .mul (slot 15) (slot 4) (slot 2)]

def code (mode : Nat) : Prog isa :=
 if mode>=9 then .seq wfront <| .seq (oddTable (if mode>=14 then 6 else 5)) <| .seq (joint (if mode=14 then 8 else if mode=15 then 7 else if mode<=10 then 5 else mode-5) (if mode>=14 then 6 else 5) (mode>=10)) <| .seq jointCross wfinish else
 .seq wfront <| .seq (if mode>=7 then oddTable (mode-2) else table) <| .seq sBase <|
 .seq (if mode=0 then kWindows else if mode=1 then windows false else if mode=2 then windows true
 else if mode<6 then sparse mode else trimmed (if mode=6 then 5 else mode-2) (mode>=7)) <| .seq wcross wfinish
end TrialEd448

def scalarCallee : VG.Impl.Sha3.AArch64.Callee := Id.run do
 let c : VG.Impl.Sha3.AArch64.Callee := ⟨"vg_keccak_f1600", VG.Impl.Sha3.AArch64.Scalar.unrolledPermute,"", false, none⟩
 return { c with absorbOverride := some (VG.Impl.Sha3.AArch64.Sha3.Vector.Resident.absorbWith VG.Impl.Sha3.AArch64.Scalar.Resident.bulk c) }
def sha3Callee : VG.Impl.Sha3.AArch64.Callee := Id.run do
 let c : VG.Impl.Sha3.AArch64.Callee := ⟨"vg_keccak_f1600_sha3", VG.Impl.Sha3.AArch64.Sha3.Vector.permute,"_sha3", true, none⟩
 return { c with absorbOverride := some (VG.Impl.Sha3.AArch64.Sha3.Vector.Resident.absorb c) }
def replaceEquation (mode : Nat) (tag : String) : Prog isa → Prog isa
 | .call n b => if n="vg_ed448_verify_equation" then .call (n++tag) (TrialEd448.code mode)
   else .call (n++tag) (replaceEquation mode tag b)
 | .seq a b => .seq (replaceEquation mode tag a) (replaceEquation mode tag b)
 | .ite c a b => .ite c (replaceEquation mode tag a) (replaceEquation mode tag b)
 | .loop b c => .loop (replaceEquation mode tag b) c
 | .frame a b c => .frame a (replaceEquation mode tag b) c
 | .block is => .block is

def emitFunction (elf : Bool) (name : String) (p : Prog isa) : String :=
 ".p2align 6\n.globl " ++ (if elf then "" else "_") ++ name ++ "\n" ++ (if elf then "" else "_") ++ name ++ ":\n" ++
 String.intercalate "\n" ((printer.function p).map fun l => match l with
 | .text s => s | .call n => "bl " ++ (if elf then "" else "_") ++ n
 | .sym s .page n => if elf then s ++ n else s ++ "_" ++ n ++ "@PAGE"
 | .sym s .pageOff n => if elf then s ++ ":lo12:" ++ n else s ++ "_" ++ n ++ "@PAGEOFF"
 | .sym .. => "UNEXPECTED_SYMBOL") ++ "\n"
partial def functions (name : String) (p : Prog isa) (seen : List String) : List (String × Prog isa) := Id.run do
 if name ∈ seen then return []
 let rec go (q : Prog isa) (seen : List String) : List (String × Prog isa) :=
   match q with
   | .call n b => functions n b seen
   | .seq a b | .ite _ a b => let xs := go a seen; xs ++ go b (seen ++ xs.map Prod.fst)
   | .loop b _ | .frame _ b _ => go b seen
   | .block _ => []
 return [(name,p)] ++ go p (name::seen)
def main (args : List String) : IO Unit := do
 let elf := args.contains "linux"
 let raw := (List.range 16).flatMap fun i => functions ("ed448_trial_" ++ toString i) (TrialEd448.code i) []
 let whole := ([0,14].flatMap fun i => [false,true].flatMap fun sha3 =>
  let tag := "_trial" ++ toString i ++ (if sha3 then "_sha3" else "")
  functions ("ed448_whole"++tag)
   (replaceEquation i tag (VG.Impl.Ed448.AArch64.Verify.verifyWith (if sha3 then sha3Callee else scalarCallee))) [])
 let fs := raw ++ whole
 let unique := fs.foldl (fun acc item => if acc.any (fun x => x.1 = item.1) then acc else acc ++ [item]) []
 let bpoints := (List.range 128).map fun i =>
   let p := Spec.Ed448.pointMul i Spec.Ed448.basePoint
   let zinv := Spec.X448.pow p.Z (Spec.X448.P-2)
   (p.X*zinv,p.Y*zinv)
 let bwords := (List.range 128).flatMap fun i =>
   let e := bpoints.getD i (0,1)
   (List.range 16).map fun j => BitVec.ofNat 64 (((if j<8 then e.1 else e.2).val >>> (56*(j%8))) % 2^56)
 let btable := "\n.p2align 6\n" ++ (if elf then "" else "_") ++ "VG_ED448_PUBLIC_BASE:\n" ++ String.join (bwords.map fun w => ".quad " ++ toString w.toNat ++ "\n")
 let tbl := (if elf then ".section .rodata\n" else ".section __TEXT,__const\n") ++ ".p2align 6\n" ++ (if elf then "" else "_") ++ "VG_X448_COMB:\n" ++
   String.join (VG.Impl.X448.AArch64.Base.combWords.map (fun w => ".quad " ++ toString w.toNat ++ "\n"))
 IO.FS.writeFile "/tmp/vg-ed448-arm64/prototype.S" (".text\n.arch_extension sha3\n" ++
   String.join (unique.map fun (n,p) => emitFunction elf n p) ++ tbl ++ btable)
