import VerifiedGarbage.Impl.Scrypt.AArch64.RoMix
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
namespace Trial

def seqs (ps : List (Prog isa)) : Prog isa := ps.foldr .seq (.block [])
def mv (d a : VReg) : Instr := .vop (.mov d a)
def ext (d : VReg) (n : Nat) : Instr := .vop (.ext d d d n)
def transpose : List Instr := [
 .vop (.perm .zip1 .s4 .v16 .v0 .v1), .vop (.perm .zip2 .s4 .v17 .v0 .v1),
 .vop (.perm .zip1 .s4 .v18 .v2 .v3), .vop (.perm .zip2 .s4 .v19 .v2 .v3),
 .vop (.perm .zip1 .d2 .v0 .v16 .v18), .vop (.perm .zip2 .d2 .v1 .v16 .v18),
 .vop (.perm .zip1 .d2 .v2 .v17 .v19), .vop (.perm .zip2 .d2 .v3 .v17 .v19)]
def toCols : List Instr := [ext .v1 4,ext .v2 8,ext .v3 12] ++ transpose ++
 [ext .v1 12,ext .v2 8,ext .v3 4]
def toRows : List Instr := [ext .v1 4,ext .v2 8,ext .v3 12] ++ transpose ++
 [ext .v1 12,ext .v2 8,ext .v3 4]
-- The diagonal transpose is involutive with these two sets of rotations.
def line (d a b : VReg) (n : Nat) : List Instr := [
 .vop (.add .s4 .v20 a b),
 .vop (.shift .ushr .s4 .v21 .v20 (32-n)),
 .vop (.shift .sli .s4 .v21 .v20 n),
 .vop (.logic .eor d d .v21)]
def quarter (a b c d : VReg) : List Instr :=
 line b a d 7 ++ line c b a 9 ++ line d c b 13 ++ line a d c 18

def doubleRound : List Instr := quarter .v0 .v3 .v2 .v1 ++
 [ext .v1 4,ext .v2 8,ext .v3 12] ++ quarter .v0 .v1 .v2 .v3 ++
 [ext .v1 12,ext .v2 8,ext .v3 4]
def rounds : List Instr := (List.range 4).flatMap (fun _ => doubleRound)

def load : List Instr := [.ldrq .v0 .x0 0,.ldrq .v1 .x0 16,.ldrq .v2 .x0 32,.ldrq .v3 .x0 48]
def remember : List Instr := [mv .v4 .v0,mv .v5 .v1,mv .v6 .v2,mv .v7 .v3]
def feed : List Instr := [.vop (.add .s4 .v0 .v0 .v4),.vop (.add .s4 .v1 .v1 .v5),
 .vop (.add .s4 .v2 .v2 .v6),.vop (.add .s4 .v3 .v3 .v7)]
def store (r : Reg) : List Instr := [.strq .v0 r 0,.strq .v1 r 16,.strq .v2 r 32,.strq .v3 r 48]
def core : List Instr := remember ++ toCols ++ rounds ++ toRows ++ feed

def neon : Prog isa := .block (load ++ core ++ store .x0)
def neonLoop : Prog isa := seqs [.block (load ++ remember ++ toCols ++ [.movz .x .x2 4 0]),
 .loop (.block (doubleRound ++ [.subImm .x .x2 .x2 1])) (.nonzero .x .x2),
 .block (toRows ++ feed ++ store .x0)]

def scalar := VG.Impl.Scrypt.AArch64.salsa
partial def rename (old n : String) : Prog isa → Prog isa
 | .block is => .block is
 | .seq a b => .seq (rename old n a) (rename old n b)
 | .ite c a b => .ite c (rename old n a) (rename old n b)
 | .loop a c => .loop (rename old n a) c
 | .frame a b c => .frame a (rename old n b) c
 | .call name b => .call (if name = old then n else name) (rename old n b)

def xorInput : List Instr := [.ldrq .v16 .x0 0,.ldrq .v17 .x0 16,
 .ldrq .v18 .x0 32,.ldrq .v19 .x0 48,
 .vop (.logic .eor .v0 .v0 .v16),.vop (.logic .eor .v1 .v1 .v17),
 .vop (.logic .eor .v2 .v2 .v18),.vop (.logic .eor .v3 .v3 .v19)]
def fusedSetup : List Instr := [.lsl .x .x5 .x1 6,.add .x .x6 .x2 .x5,
 .lsl .x .x5 .x1 7,.add .x .x5 .x0 .x5,.subImm .x .x5 .x5 64,
 .ldrq .v0 .x5 0,.ldrq .v1 .x5 16,.ldrq .v2 .x5 32,.ldrq .v3 .x5 48]
def fusedStep (out : Reg) : List Instr := xorInput ++ core ++ store out ++ [.addImm .x .x0 .x0 64]
def fused : Prog isa := .seq (.block fusedSetup)
 (.loop (.block (fusedStep .x2 ++ fusedStep .x6 ++
 [.addImm .x .x2 .x2 64,.addImm .x .x6 .x6 64,.subImm .x .x1 .x1 1])) (.nonzero .x .x1))

def fusedLoopCore : Prog isa := .seq (.block (remember ++ toCols ++ [.movz .x .x7 4 0]))
 (.seq (.loop (.block (doubleRound ++ [.subImm .x .x7 .x7 1])) (.nonzero .x .x7)) (.block (toRows ++ feed)))
def fusedLoopStep (out : Reg) : Prog isa := seqs [.block xorInput,fusedLoopCore,
 .block (store out ++ [.addImm .x .x0 .x0 64])]
def fusedLoop : Prog isa := .seq (.block fusedSetup)
 (.loop (seqs [fusedLoopStep .x2,fusedLoopStep .x6,
 .block [.addImm .x .x2 .x2 64,.addImm .x .x6 .x6 64,.subImm .x .x1 .x1 1]]) (.nonzero .x .x1))

def scalarFoldLine (i j k n : Nat) : List Instr :=
 [.add .w .x1 (VG.Impl.Scrypt.AArch64.wreg j) (VG.Impl.Scrypt.AArch64.wreg k),
  .logicRor .eor .w (VG.Impl.Scrypt.AArch64.wreg i) (VG.Impl.Scrypt.AArch64.wreg i) .x1 (32-n)]
def scalarFoldCore : List Instr := (List.range 4).flatMap (fun _ =>
 VG.Impl.Scrypt.AArch64.lines.flatMap (fun (i,j,k,n) => scalarFoldLine i j k n))
def scalarFold : Prog isa := .block
 (VG.Impl.Scrypt.AArch64.load ++ scalarFoldCore ++ VG.Impl.Scrypt.AArch64.finish)
def vectorXor (dst x src : Reg) : List Instr := (List.range 4).flatMap (fun k =>
 [.ldrq .v0 x (16*k),.ldrq .v1 src (16*k),.vop (.logic .eor .v0 .v0 .v1),.strq .v0 dst (16*k)])
def vectorBmBody (s : Prog isa) : Prog isa := seqs [
 .block (vectorXor .x20 .x24 .x19),
 VG.Impl.Scrypt.AArch64.salsaAt s .x20,
 .block (.addImm .x .x19 .x19 64 :: vectorXor .x21 .x20 .x19),
 VG.Impl.Scrypt.AArch64.salsaAt s .x21,
 .block [VG.Impl.Scrypt.AArch64.mov .x24 .x21,.addImm .x .x19 .x19 64,
 .addImm .x .x20 .x20 64,.addImm .x .x21 .x21 64,.subImm .x .x23 .x23 1]]
def vectorBm (s : Prog isa) : Prog isa := .frame (.push .x30)
 (seqs [.block VG.Impl.Scrypt.AArch64.bmPrologue,
 .loop (vectorBmBody s) (.nonzero .x .x23),.block VG.Impl.Scrypt.AArch64.bmEpilogue]) (.pop .x30)

def inlineBmBody (s : Prog isa) : Prog isa := seqs [
 .block (vectorXor .x20 .x24 .x19 ++ [VG.Impl.Scrypt.AArch64.mov .x0 .x20]),s,
 .block (.addImm .x .x19 .x19 64 :: vectorXor .x21 .x20 .x19 ++ [VG.Impl.Scrypt.AArch64.mov .x0 .x21]),s,
 .block [VG.Impl.Scrypt.AArch64.mov .x24 .x21,.addImm .x .x19 .x19 64,
 .addImm .x .x20 .x20 64,.addImm .x .x21 .x21 64,.subImm .x .x23 .x23 1]]
def inlineBm (s : Prog isa) : Prog isa := seqs [.block VG.Impl.Scrypt.AArch64.bmPrologue,
 .loop (inlineBmBody s) (.nonzero .x .x23),.block VG.Impl.Scrypt.AArch64.bmEpilogue]

def ioLoad : List Instr := (List.range 4).flatMap (fun k =>
 [.ldrq (#[.v4,.v5,.v6,.v7].getD k .v4) .x0 (16*k)])
def toGprs : List Instr := (List.range 8).flatMap (fun k =>
 [.umov .x (VG.Impl.Scrypt.AArch64.wreg (2*k)) (#[.v4,.v5,.v6,.v7].getD (k/2) .v4) (k%2),
  .lsr .x (VG.Impl.Scrypt.AArch64.wreg (2*k+1)) (VG.Impl.Scrypt.AArch64.wreg (2*k)) 32])
def fromGprs : List Instr := (List.range 8).flatMap (fun k =>
 [.lsl .x .x1 (VG.Impl.Scrypt.AArch64.wreg (2*k+1)) 32,
 .logic .orr .x .x1 .x1 (VG.Impl.Scrypt.AArch64.wreg (2*k)),
 .vop (.ins .d2 (#[.v0,.v1,.v2,.v3].getD (k/2) .v0) (k%2) .x1)])
def ioFinish : List Instr := fromGprs ++ [
 .vop (.add .s4 .v0 .v0 .v4),.vop (.add .s4 .v1 .v1 .v5),
 .vop (.add .s4 .v2 .v2 .v6),.vop (.add .s4 .v3 .v3 .v7)] ++ store .x0

def scalarIo : Prog isa := .block (ioLoad ++ toGprs ++ scalarFoldCore ++ ioFinish)

def scheduledLines : List (Nat × Nat × Nat × Nat) := [0,16].flatMap (fun off =>
 (List.range 4).flatMap (fun stage => (List.range 4).map (fun q =>
 VG.Impl.Scrypt.AArch64.lines.getD (off+4*q+stage) (0,0,0,1))))
def scheduled (fold : Bool) : Prog isa := .block
 (VG.Impl.Scrypt.AArch64.load ++ (List.range 4).flatMap (fun _ =>
 scheduledLines.flatMap (fun (i,j,k,n) => if fold then scalarFoldLine i j k n else
 VG.Impl.Scrypt.AArch64.line i j k n)) ++ VG.Impl.Scrypt.AArch64.finish)
def vcopyLoop (u : Nat) : Prog isa := .loop (.block (
 (List.range u).map (fun k => Instr.ldrq (#[.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7].getD k .v0) .x9 (16*k)) ++
 (List.range u).map (fun k => Instr.strq (#[.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7].getD k .v0) .x10 (16*k)) ++
 [.addImm .x .x9 .x9 (16*u),.addImm .x .x10 .x10 (16*u),.subImm .x .x11 .x11 (2*u)])) (.nonzero .x .x11)
def vxorLoop (u : Nat) : Prog isa := .loop (.block (
 (List.range u).map (fun k => Instr.ldrq (#[.v0,.v1,.v2,.v3].getD k .v0) .x9 (16*k)) ++
 (List.range u).map (fun k => Instr.ldrq (#[.v4,.v5,.v6,.v7].getD k .v4) .x10 (16*k)) ++
 (List.range u).map (fun k => Instr.vop (.logic .eor (#[.v0,.v1,.v2,.v3].getD k .v0)
 (#[.v0,.v1,.v2,.v3].getD k .v0) (#[.v4,.v5,.v6,.v7].getD k .v4))) ++
 (List.range u).map (fun k => Instr.strq (#[.v0,.v1,.v2,.v3].getD k .v0) .x11 (16*k)) ++
 [.addImm .x .x9 .x9 (16*u),.addImm .x .x10 .x10 (16*u),.addImm .x .x11 .x11 (16*u),
 .subImm .x .x12 .x12 (2*u)])) (.nonzero .x .x12)
open VG.Impl.Scrypt.AArch64 in
def rmWith (copy xor bm : Prog isa) : Prog isa :=
 let step2 := seqs [.block [mov .x9 .x19,mov .x10 .x24,.lsr .x .x11 .x22 3],copy,
 blockMixTo bm [mov .x0 .x24],.block [.add .x .x24 .x24 .x22,.subImm .x .x23 .x23 1]]
 let step3 := seqs [.block jBlock,.block [.madd .x .x10 .x9 .x22 .x20,mov .x9 .x19,
 .addImm .x .x11 .x21 192,.lsr .x .x12 .x22 3],xor,
 blockMixTo bm [.addImm .x .x0 .x21 192],.block [.subImm .x .x23 .x23 1]]
 seqs [.block rmPrologue,nLoop,.block rmSetup,.loop step2 (.nonzero .x .x23),
 .block rmMid,.loop step3 (.nonzero .x .x23),.block rmEpilogue]

def sv (k : Nat) : VReg :=
 #[.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23].getD k .v0
def residentSaved : List (Reg × VReg) := [(.x19,.v24),(.x20,.v25),(.x21,.v26),(.x22,.v27)]
def residentSetup : List Instr := residentSaved.map (fun (r,v) => .vop (.dup .d2 v r)) ++
 [VG.Impl.Scrypt.AArch64.mov .x21 .x1,VG.Impl.Scrypt.AArch64.mov .x19 .x2,
 .lsl .x .x22 .x1 6,.add .x .x20 .x2 .x22,.lsl .x .x22 .x1 7,
 .add .x .x22 .x0 .x22,.subImm .x .x22 .x22 64] ++
 (List.range 16).map (fun k => Instr.ldr .w (VG.Impl.Scrypt.AArch64.wreg k) .x22 (4*k))
def residentStep (mode : Nat) (out : Reg) : List Instr :=
 (List.range 16).flatMap (fun k =>
 [.ldr .w .x22 .x0 (4*k),.logic .eor .w (VG.Impl.Scrypt.AArch64.wreg k) (VG.Impl.Scrypt.AArch64.wreg k) .x22] ++
 (if mode = 0 then [.str .w (VG.Impl.Scrypt.AArch64.wreg k) out (4*k)]
 else if mode = 1 then [.vop (.ins .s4 (sv (k/4)) (k%4) (VG.Impl.Scrypt.AArch64.wreg k))]
 else [.vop (.dup .s4 (sv k) (VG.Impl.Scrypt.AArch64.wreg k))])) ++
 (List.range 4).flatMap (fun _ => VG.Impl.Scrypt.AArch64.lines.flatMap (fun (i,j,k,n) => VG.Impl.Scrypt.AArch64.line i j k n)) ++
 (List.range 16).flatMap (fun k =>
 (if mode = 0 then [.ldr .w .x1 out (4*k)]
 else if mode = 1 then [.umov .w .x1 (sv (k/4)) (k%4)] else [.umov .w .x1 (sv k) 0]) ++
 [.add .w (VG.Impl.Scrypt.AArch64.wreg k) (VG.Impl.Scrypt.AArch64.wreg k) .x1,
 .str .w (VG.Impl.Scrypt.AArch64.wreg k) out (4*k)]) ++ [.addImm .x .x0 .x0 64]
def resident (mode : Nat) : Prog isa := seqs [.block residentSetup,
 .loop (.block (residentStep mode .x19 ++ residentStep mode .x20 ++
 [.addImm .x .x19 .x19 64,.addImm .x .x20 .x20 64,.subImm .x .x21 .x21 1])) (.nonzero .x .x21),
 .block (residentSaved.map (fun (r,v) => Instr.umov .x r v 0))]

def bmVariants : List (String × Prog isa) := [
 ("scalar",rename "vg_salsa20_8" "trial_scalar" (VG.Impl.Scrypt.AArch64.blockMixWith scalar)),
 ("neon",rename "vg_salsa20_8" "trial_neon" (VG.Impl.Scrypt.AArch64.blockMixWith neon)),
 ("neon_loop",rename "vg_salsa20_8" "trial_neon_loop" (VG.Impl.Scrypt.AArch64.blockMixWith neonLoop)),
 ("fused",fused),("fused_loop",fusedLoop),("resident_mem",resident 0),("resident_ins",resident 1),("resident_dup",resident 2),
 ("fold",rename "vg_salsa20_8" "trial_fold" (VG.Impl.Scrypt.AArch64.blockMixWith scalarFold)),
 ("fold_vcopy",rename "vg_salsa20_8" "trial_fold" (vectorBm scalarFold)),
 ("fold_inline",inlineBm scalarFold),
 ("fold_io",inlineBm scalarIo),
 ("schedule",rename "vg_salsa20_8" "trial_schedule" (VG.Impl.Scrypt.AArch64.blockMixWith (scheduled false))),
 ("schedule_fold",rename "vg_salsa20_8" "trial_schedule_fold" (VG.Impl.Scrypt.AArch64.blockMixWith (scheduled true)))]
def variants : List (String × Prog isa) := [("trial_scalar",scalar),("trial_neon",neon),("trial_neon_loop",neonLoop),
 ("trial_fold",scalarFold),("trial_fold_io",scalarIo),("trial_schedule",scheduled false),("trial_schedule_fold",scheduled true)] ++
 bmVariants.map (fun (n,b) => ("trial_bm_"++n,b)) ++
 bmVariants.map (fun (n,b) => ("trial_rm_" ++ n, rename "vg_scrypt_blockmix" ("trial_bm_" ++ n) (VG.Impl.Scrypt.AArch64.roMixWith b)))
def more : List (String × Prog isa) := [1,2,4].flatMap (fun u =>
 [("scalar",rename "vg_salsa20_8" "trial_scalar" (VG.Impl.Scrypt.AArch64.blockMixWith scalar)),
 ("schedule",rename "vg_salsa20_8" "trial_schedule" (VG.Impl.Scrypt.AArch64.blockMixWith (scheduled false))),("resident_mem",resident 0),("resident_ins",resident 1),("resident_dup",resident 2)].map (fun (n,b) =>
 ("trial_rm_" ++ n ++ "_v" ++ toString u,rename "vg_scrypt_blockmix" ("trial_bm_"++n) (rmWith (vcopyLoop u) (vxorLoop u) b))))
def emit (name : String) (p : Prog isa) (apple : Bool) : String :=
 let pre := if apple then "_" else ""
 ".p2align 6\n.globl " ++ pre ++ name ++ "\n" ++ pre ++ name ++ ":\n" ++
 String.intercalate "\n" ((printer.function p).map fun l => match l with
 | .text s => s | .call n => "bl " ++ pre ++ n | .sym .. => "ERROR_SYMBOL") ++ "\n"
def main : IO Unit := do
 for apple in [true,false] do
  IO.FS.writeFile ("/tmp/vg-scrypt-neon/prototypes-" ++ (if apple then "apple" else "linux") ++ ".S")
   (".text\n" ++ String.join ((variants ++ more).map fun (n,p) => emit n p apple))
end Trial
def main := Trial.main
