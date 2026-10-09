import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.HighPack

namespace VG.Impl.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Round
open VG.Impl.MlDsa.AArch64.Optimized.HighPack

def cadd (d : VReg) : List Instr :=
  [.vop (.shift .sshr .s4 .v7 d 31),.vop (.logic .and .v7 .v7 .v16),.vop (.add .s4 d d .v7)]
def loop (ptrs : List Reg) (body : Nat → List Instr) : Prog isa :=
  .seq (.block [.movz .x .x10 16 0])
    (.loop (.block (([0,16,32,48].flatMap body) ++
      ptrs.map (fun r => .addImm .x r r 64) ++ [.subImm .x .x10 .x10 1])) (.nonzero .x .x10))
def finish : Prog isa := .block [
  .umov .w .x0 .v31 0,.umov .w .x9 .v31 1,.logic .orr .w .x0 .x0 .x9,
  .umov .w .x9 .v31 2,.logic .orr .w .x0 .x0 .x9,.umov .w .x9 .v31 3,
  .logic .orr .w .x0 .x0 .x9,.addImm .w .x0 .x0 1]

-- v25=2^22, v16=q. v6 temporary; result congruent modulo q.
def reduce (d : VReg) : List Instr :=
 [.vop (.add .s4 .v6 d .v25),.vop (.shift .sshr .s4 .v6 .v6 23),.vop (.mls d .v6 .v16)]
def normConstants : List Instr := vc .v27 1 ++
 [.vop (.sub .s4 .v27 .v24 .v27),.vop (.add .s4 .v24 .v24 .v27)]
def testNorm : List Instr :=
 [.vop (.add .s4 .v2 .v0 .v27),.vop (.umin .v2 .v2 .v24),
 .vop (.cmeq .s4 .v2 .v2 .v24),.vop (.logic .orr .v31 .v31 .v2)]
def addNorm : Prog isa :=
 .seq (.block (vc .v16 8380417 ++ vc .v25 (2^22) ++
 [.vop (.dup .s4 .v24 .x2),.vop (.movi0 .v31)] ++ normConstants)) <|
 .seq (loop [.x0,.x1] fun off => [.ldrq .v0 .x0 off,.ldrq .v1 .x1 off,
 .vop (.add .s4 .v0 .v0 .v1)] ++ reduce .v0 ++ [.strq .v0 .x0 off] ++ testNorm)
 finish
-- Canonical input w; signed raw cs; high output overwrites w, signed low to x2.
def subLowNorm : Prog isa :=
 zext .x3 <| onGamma .x3 .x5 fun g =>
 .seq (.block (constants g ++ vc .v25 (2^22) ++ vc .v26 4190208 ++
 [.vop (.dup .s4 .v24 .x4),.vop (.movi0 .v31)] ++ normConstants)) <|
 .seq (loop [.x0,.x1,.x2] fun off => [.ldrq .v0 .x0 off,.ldrq .v1 .x1 off,
 .vop (.sub .s4 .v0 .v0 .v1)] ++ reduce .v0 ++ cadd .v0 ++
 hb g .v1 .v0 ++ [.strq .v1 .x0 off,.vop (.mls .v0 .v1 .v21),
 -- For the exceptional wrapped high=0, subtract q from the large positive low.
 .vop (.sub .s4 .v6 .v26 .v0),.vop (.shift .sshr .s4 .v6 .v6 31),
 .vop (.logic .and .v6 .v6 .v16),.vop (.sub .s4 .v0 .v0 .v6),
 .strq .v0 .x2 off] ++ testNorm) finish
-- Signed low -> hints; signed raw ct; canonical high. u64 count | validNorm<<32.
def hintNorm : Prog isa :=
 .seq (.block (vc .v16 8380417 ++ vc .v25 (2^22) ++
 [.vop (.dup .s4 .v24 .x3),.vop (.dup .s4 .v17 .x3),
 .vop (.movi0 .v23),.vop (.sub .s4 .v18 .v23 .v17),
 .vop (.movi0 .v30),.vop (.movi0 .v31)] ++ normConstants)) <|
 .seq (loop [.x0,.x1,.x2] fun off =>
 [.ldrq .v0 .x1 off,.ldrq .v3 .x0 off,.ldrq .v4 .x2 off] ++ reduce .v0 ++ testNorm ++
 [.vop (.add .s4 .v0 .v0 .v3),
 -- negative masks for gamma-t and t+gamma implement strict outside interval.
 .vop (.sub .s4 .v2 .v17 .v0),.vop (.sub .s4 .v3 .v0 .v18),
 .vop (.logic .orr .v2 .v2 .v3),.vop (.shift .sshr .s4 .v2 .v2 31),
 .vop (.cmeq .s4 .v3 .v0 .v18),.vop (.cmeq .s4 .v4 .v4 .v23),
 .vop (.logic .bic .v3 .v3 .v4),.vop (.logic .orr .v2 .v2 .v3),
 .vop (.shift .ushr .s4 .v2 .v2 31),.strq .v2 .x0 off,.vop (.add .s4 .v30 .v30 .v2)]) <|
 .block [.umov .w .x1 .v31 0,.umov .w .x9 .v31 1,.logic .orr .w .x1 .x1 .x9,
 .umov .w .x9 .v31 2,.logic .orr .w .x1 .x1 .x9,.umov .w .x9 .v31 3,.logic .orr .w .x1 .x1 .x9,.addImm .w .x1 .x1 1,
 .umov .w .x0 .v30 0,.umov .w .x9 .v30 1,.add .w .x0 .x0 .x9,
 .umov .w .x9 .v30 2,.add .w .x0 .x0 .x9,.umov .w .x9 .v30 3,.add .w .x0 .x0 .x9,
 .lsl .x .x1 .x1 32,.logic .orr .x .x0 .x0 .x1]
-- Called only at accepted output: signed z in (-gamma1,gamma1), to canonical residues.
def canonicalize : Prog isa := .seq (.block (vc .v16 8380417)) <|
 loop [.x0] fun off => [.ldrq .v0 .x0 off] ++ cadd .v0 ++ [.strq .v0 .x0 off]
end VG.Impl.MlDsa.AArch64.Optimized.Response
