import VerifiedGarbage.Impl.Blake2.AArch64
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64 VG.Impl.Blake2.AArch64
namespace Trial
def seqs (ps : List (Prog isa)) : Prog isa := ps.foldr .seq (.block [])
def regs (diag : Bool) (i : Nat) : List Reg :=
 (if diag then [[0,5,10,15],[1,6,11,12],[2,7,8,13],[3,4,9,14]] else
 [[0,4,8,12],[1,5,9,13],[2,6,10,14],[3,7,11,15]]).getD i [] |>.map wreg
def piece {w} (P : Spec.Blake2.Params w) (r : Nat) (diag : Bool) (i stage : Nat) (early : Bool) : List Instr := Id.run do
 let rs := regs diag i
 let a := rs.getD 0 .x3; let b := rs.getD 1 .x3
 let c := rs.getD 2 .x3; let d := rs.getD 3 .x3
 let j := Spec.Blake2.sigmaAt r (8*(if diag then 1 else 0) + 2*i + (if stage < 6 then 0 else 1))
 match stage % 6 with
 | 0 => return if early then [.ldr (sz w) T .x1 (ws w*j),.add (sz w) a a T,.add (sz w) a a b]
        else [.ldr (sz w) T .x1 (ws w*j),.add (sz w) a a b,.add (sz w) a a T]
 | 1 => return [.logic .eor (sz w) d d a]
 | 2 => return [.ror (sz w) d d (if stage < 6 then P.R1 else P.R3)]
 | 3 => return [.add (sz w) c c d]
 | 4 => return [.logic .eor (sz w) b b c]
 | _ => return [.ror (sz w) b b (if stage < 6 then P.R2 else P.R4)]
def roundTrial {w} (P : Spec.Blake2.Params w) (r width : Nat) (early : Bool) : Prog isa :=
 .block ([false,true].flatMap fun diag => (List.range (4 / width)).flatMap fun group =>
 (List.range 12).flatMap fun stage => (List.range width).flatMap fun lane => piece P r diag (group*width+lane) stage early)
def trial {w} (P : Spec.Blake2.Params w) (width : Nat) (early : Bool) : Prog isa :=
 .seq (.block (save ++ setup))
  (.seq (.ite (.zero .x .x2) (.block []) (.loop
   (seqs [init P,seqs ((List.range P.r).map fun r => roundTrial P r width early),fin (w := w) 8,.block (advance (w := w))])
   (.nonzero .x .x2))) (.block restore))
def vr (i : Nat) : VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23,.v24,.v25,.v26,.v27,.v28,.v29,.v30,.v31].getD i .v0
def arr (w : Nat) : VArr := if w=64 then .d2 else .s4
def lanes (w : Nat) : Nat := 128/w
def vx (d n m : VReg) : Instr := .vop (.logic .eor d n m)
def rot (w : Nat) (d : VReg) (r : Nat) : List Instr :=
 if w=64 && r=32 then [.vop (.rev .rev64s d d)]
 else if w=32 && r=16 then [.vop (.rev .rev32h d d)]
 else [.vop (.shift .ushr (arr w) .v18 d r),.vop (.shift .sli (arr w) .v18 d (w-r)),.vop (.mov d .v18)]
def msg {w : Nat} (r : Nat) (diag : Bool) (half group : Nat) : List Instr :=
 (List.range (lanes w)).map fun lane =>
 let i := group * lanes w + lane
 let j := (Spec.Blake2.sigmaAt r ((if diag then 8 else 0)+2*i+half)).val
 .vop (.insE (arr w) (vr (8+group)) lane (vr (16+j/lanes w)) (j%lanes w))
def vgHalf {w} (P : Spec.Blake2.Params w) (r : Nat) (diag : Bool) (half : Nat) : List Instr := Id.run do
 let groups := 4 / lanes w
 let mut is := (List.range groups).flatMap (msg (w := w) r diag half)
 for group in List.range groups do
  let a := vr group; let b := vr (groups+group); let c := vr (2*groups+group); let d := vr (3*groups+group)
  is := is ++ [.vop (.add (arr w) a a (vr (8+group))),.vop (.add (arr w) a a b),vx d d a] ++
   rot w d (if half=0 then P.R1 else P.R3) ++ [.vop (.add (arr w) c c d),vx b b c] ++
   rot w b (if half=0 then P.R2 else P.R4)
 return is
def diagPerm (w : Nat) (back : Bool) : List Instr :=
 if w=32 then (List.range 3).map fun i =>
  let k := (i+1)*4
  .vop (.ext (vr (i+1)) (vr (i+1)) (vr (i+1)) (if back then 16-k else k))
 else (List.range 3).flatMap fun i =>
  let shift := if back then (4-(i+1))%4 else i+1
  let a := vr (2*(i+1)); let b := vr (2*(i+1)+1)
  if shift=2 then [.vop (.mov .v16 a),.vop (.mov a b),.vop (.mov b .v16)]
  else if shift=1 then [.vop (.ext .v16 a b 8),.vop (.ext b b a 8),.vop (.mov a .v16)]
  else [.vop (.ext .v16 b a 8),.vop (.ext b a b 8),.vop (.mov a .v16)]
def vectorTrial {w} (P : Spec.Blake2.Params w) : Prog isa := Id.run do
 let pack := (List.range 16).map fun i => .vop (.ins (arr w) (vr (i/lanes w)) (i%lanes w) (wreg i))
 let unpack := (List.range 16).map fun i => .umov (sz w) (wreg i) (vr (i/lanes w)) (i%lanes w)
 let loads := (List.range (16/lanes w)).map fun i => .ldrq (vr (16+i)) .x1 (16*i)
 let rounds := (List.range P.r).flatMap fun r => vgHalf P r false 0 ++ vgHalf P r false 1 ++ diagPerm w false ++
  vgHalf P r true 0 ++ vgHalf P r true 1 ++ diagPerm w true
 return .seq (.block (save ++ setup)) (.seq (.ite (.zero .x .x2) (.block []) (.loop
  (seqs [init P,.block (pack ++ loads ++ rounds ++ unpack),fin (w := w) 8,.block (advance (w := w))])
  (.nonzero .x .x2))) (.block restore))
def emit (name : String) (p : Prog isa) (apple : Bool) : String :=
 let pre := if apple then "_" else ""
 ".p2align 6\n.globl " ++ pre ++ name ++ "\n" ++ pre ++ name ++ ":\n" ++
 String.intercalate "\n" ((printer.function p).map fun l => match l with
 | .text s => s | .call n => "bl " ++ pre ++ n | .sym .. => "ERROR_SYMBOL") ++ "\n"
def main : IO Unit := do
 for apple in [true,false] do
  let variants := [("base_b",compress Spec.Blake2.b),("base_s",compress Spec.Blake2.s),("bneon",vectorTrial Spec.Blake2.b),("sneon",vectorTrial Spec.Blake2.s)] ++
   [1,2,4].flatMap (fun width => [false,true].flatMap (fun early =>
    [("b",trial Spec.Blake2.b width early),("s",trial Spec.Blake2.s width early)].map fun (n,c) =>
     (n ++ toString width ++ (if early then "early" else ""),c)))
  IO.FS.writeFile ("/tmp/vg-blake2-arm64/prototypes-" ++ (if apple then "apple" else "linux") ++ ".S")
   (".text\n" ++ String.join (variants.map fun (n,p) => emit n p apple))
end Trial
def main := Trial.main
