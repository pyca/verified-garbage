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

def variants : List (String × Prog isa) := [("trial_scalar",scalar),("trial_neon",neon),("trial_neon_loop",neonLoop),
 ("trial_bm_scalar",rename "vg_salsa20_8" "trial_scalar" (VG.Impl.Scrypt.AArch64.blockMixWith scalar)),
 ("trial_bm_neon",rename "vg_salsa20_8" "trial_neon" (VG.Impl.Scrypt.AArch64.blockMixWith neon)),
 ("trial_bm_neon_loop",rename "vg_salsa20_8" "trial_neon_loop" (VG.Impl.Scrypt.AArch64.blockMixWith neonLoop)),
 ("trial_bm_fused",fused),("trial_bm_fused_loop",fusedLoop)] ++
 [("scalar",rename "vg_salsa20_8" "trial_scalar" (VG.Impl.Scrypt.AArch64.blockMixWith scalar)),("neon",rename "vg_salsa20_8" "trial_neon" (VG.Impl.Scrypt.AArch64.blockMixWith neon)),("neon_loop",rename "vg_salsa20_8" "trial_neon_loop" (VG.Impl.Scrypt.AArch64.blockMixWith neonLoop)),("fused",fused),("fused_loop",fusedLoop)].map (fun (n,b) =>
  ("trial_rm_" ++ n, rename "vg_scrypt_blockmix" ("trial_bm_" ++ n) (VG.Impl.Scrypt.AArch64.roMixWith b)))
def emit (name : String) (p : Prog isa) (apple : Bool) : String :=
 let pre := if apple then "_" else ""
 ".p2align 6\n.globl " ++ pre ++ name ++ "\n" ++ pre ++ name ++ ":\n" ++
 String.intercalate "\n" ((printer.function p).map fun l => match l with
 | .text s => s | .call n => "bl " ++ pre ++ n | .sym .. => "ERROR_SYMBOL") ++ "\n"
def main : IO Unit := do
 for apple in [true,false] do
  IO.FS.writeFile ("/tmp/vg-scrypt-neon/prototypes-" ++ (if apple then "apple" else "linux") ++ ".S")
   (".text\n" ++ String.join (variants.map fun (n,p) => emit n p apple))
end Trial
def main := Trial.main
