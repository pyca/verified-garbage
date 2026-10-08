import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Variants.Keccak.AArch64.Sha3
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
namespace CombRound
open VG.Impl.MlDsa.AArch64.Round
open VG.Impl.MlDsa.AArch64.Arith (movW)

def vc (d : VReg) (n : Nat) : List Instr :=
  movW .x9 (BitVec.ofNat 32 n) ++ [.vop (.dup .s4 d .x9)]
def constants (g : Nat) : List Instr :=
  vc .v16 8380417 ++ vc .v17 127 ++ vc .v18 (dMul g) ++
  vc .v19 (2^(dShift g-1)) ++ vc .v20 (dMod g) ++ vc .v21 (2*g) ++
  vc .v22 1 ++ [.vop (.movi0 .v23)]
def hf (g : Nat) (d a : VReg) : List Instr :=
  [.vop (.add .s4 d a .v17), .vop (.shift .ushr .s4 d d 7),
   .vop (.mul d d .v18), .vop (.add .s4 d d .v19),
   .vop (.shift .ushr .s4 d d (dShift g))]
def hb (g : Nat) (d a : VReg) : List Instr := hf g d a ++
  [.vop (.sub .s4 .v7 d .v20), .vop (.shift .sshr .s4 .v7 .v7 31),
   .vop (.logic .and d d .v7)]
def csub (d : VReg) (modulus : VReg := .v16) : List Instr :=
  [.vop (.sub .s4 .v7 d modulus), .vop (.umin d d .v7)]
def cadd (d : VReg) : List Instr :=
  [.vop (.shift .sshr .s4 .v7 d 31), .vop (.logic .and .v7 .v7 .v16),
   .vop (.add .s4 d d .v7)]
def loop (ptrs : List Reg) (body : Nat → List Instr) : Prog isa :=
  .seq (.block [.movz .x .x10 16 0])
   (.loop (.block (([0,16,32,48].flatMap body) ++
     ptrs.map (fun r => .addImm .x r r 64) ++ [.subImm .x .x10 .x10 1])) (.nonzero .x .x10))
def bits (low : Bool) : Prog isa :=
  zext .x1 <| onGamma .x1 .x3 fun g => .seq (.block (constants g)) <|
   loop [.x0,.x2] fun off => [.ldrq .v0 .x0 off] ++ hb g .v1 .v0 ++
     (if low then [.vop (.mls .v0 .v1 .v21)] ++ cadd .v0 ++ [.strq .v0 .x2 off]
      else [.strq .v1 .x2 off])
def power2Round : Prog isa :=
  .seq (.block (vc .v16 8380417 ++ vc .v17 4095)) <|
   loop [.x0,.x1,.x2] fun off => [.ldrq .v0 .x0 off,
    .vop (.add .s4 .v1 .v0 .v17), .vop (.shift .ushr .s4 .v1 .v1 13),
    .vop (.shift .shl .s4 .v2 .v1 13), .vop (.sub .s4 .v0 .v0 .v2)] ++
    cadd .v0 ++ [.strq .v1 .x1 off,.strq .v0 .x2 off]
def normLt : Prog isa :=
 .seq (.block (vc .v16 8380417 ++ [.vop (.dup .s4 .v17 .x1), .vop (.movi0 .v31)])) <|
 .seq (loop [.x0] fun off => [.ldrq .v0 .x0 off,
   .vop (.sub .s4 .v1 .v16 .v0), .vop (.umin .v0 .v0 .v1),
   .vop (.umin .v1 .v0 .v17), .vop (.cmeq .s4 .v1 .v1 .v17),
   .vop (.logic .orr .v31 .v31 .v1)]) <|
 .block [.umov .w .x0 .v31 0,.umov .w .x9 .v31 1,.logic .orr .w .x0 .x0 .x9,
   .umov .w .x9 .v31 2,.logic .orr .w .x0 .x0 .x9,
   .umov .w .x9 .v31 3,.logic .orr .w .x0 .x0 .x9,
   .addImm .w .x0 .x0 1]
def makeHint : Prog isa :=
 zext .x2 <| .seq (onGamma .x2 .x4 fun g =>
  .seq (.block (constants g ++ [.vop (.movi0 .v31)])) <|
  loop [.x0,.x1,.x3] fun off => [.ldrq .v0 .x1 off,.ldrq .v2 .x0 off] ++
   hb g .v1 .v0 ++ [.vop (.add .s4 .v0 .v0 .v2)] ++ csub .v0 ++ hb g .v3 .v0 ++
   [.vop (.cmeq .s4 .v3 .v3 .v1), .vop (.not .v3 .v3),
    .vop (.shift .ushr .s4 .v3 .v3 31), .strq .v3 .x3 off,
    .vop (.add .s4 .v31 .v31 .v3)]) <|
 .block [.umov .w .x0 .v31 0,.umov .w .x9 .v31 1,.add .w .x0 .x0 .x9,
   .umov .w .x9 .v31 2,.add .w .x0 .x0 .x9,
   .umov .w .x9 .v31 3,.add .w .x0 .x0 .x9]
def useHint : Prog isa :=
 zext .x2 <| onGamma .x2 .x4 fun g => .seq (.block (constants g)) <|
 loop [.x0,.x1,.x3] fun off => [.ldrq .v0 .x1 off,.ldrq .v2 .x0 off] ++ hf g .v1 .v0 ++
 [.vop (.mul .v3 .v1 .v21), .vop (.sub .s4 .v3 .v3 .v0),
  .vop (.shift .ushr .s4 .v3 .v3 31), .vop (.shift .shl .s4 .v3 .v3 1),
  .vop (.sub .s4 .v3 .v3 .v22), .vop (.cmeq .s4 .v2 .v2 .v23),
  .vop (.logic .bic .v3 .v3 .v2), .vop (.add .s4 .v1 .v1 .v3),
  .vop (.add .s4 .v1 .v1 .v20)] ++ csub .v1 .v20 ++ csub .v1 .v20 ++ [.strq .v1 .x3 off]
end CombRound
namespace CombFusedCheck
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Round
open CombRound
def testNorm : List Instr :=
 [.vop (.sub .s4 .v2 .v16 .v0),.vop (.umin .v2 .v0 .v2),
 .vop (.umin .v2 .v2 .v24),.vop (.cmeq .s4 .v2 .v2 .v24),.vop (.logic .orr .v31 .v31 .v2)]
def finish : Prog isa := .block [
 .umov .w .x0 .v31 0,.umov .w .x9 .v31 1,.logic .orr .w .x0 .x0 .x9,
 .umov .w .x9 .v31 2,.logic .orr .w .x0 .x0 .x9,.umov .w .x9 .v31 3,
 .logic .orr .w .x0 .x0 .x9,.addImm .w .x0 .x0 1]
-- canonical inout=x0, canonical addend=x1, bound=w2; return bool w0.
def addNorm : Prog isa :=
 .seq (.block (vc .v16 8380417 ++ [.vop (.dup .s4 .v24 .x2),.vop (.movi0 .v31)])) <|
 .seq (loop [.x0,.x1] fun off => [.ldrq .v0 .x0 off,.ldrq .v1 .x1 off,
 .vop (.add .s4 .v0 .v0 .v1)] ++ csub .v0 ++ [.strq .v0 .x0 off] ++ testNorm) finish
-- inout=x0 (canonical input, high output), subtrahend=x1, low=x2, gamma=w3, bound=w4.
def subLowNorm : Prog isa :=
 zext .x3 <| onGamma .x3 .x5 fun g =>
 .seq (.block (constants g ++ [.vop (.dup .s4 .v24 .x4),.vop (.movi0 .v31)])) <|
 .seq (loop [.x0,.x1,.x2] fun off => [.ldrq .v0 .x0 off,.ldrq .v1 .x1 off,
 .vop (.add .s4 .v0 .v0 .v16),.vop (.sub .s4 .v0 .v0 .v1)] ++ csub .v0 ++
 hb g .v1 .v0 ++ [.strq .v1 .x0 off,.vop (.mls .v0 .v1 .v21)] ++ cadd .v0 ++
 [.strq .v0 .x2 off] ++ testNorm) finish
end CombFusedCheck
namespace CombFusedCheck
-- low→hint=x0, ct0=x1, high=x2, gamma=w3; return u64: low32=count, bit32=normflag.
def hintNorm : Prog isa :=
 .seq (.block (CombRound.vc .v16 8380417 ++
 [.vop (.dup .s4 .v24 .x3),.vop (.dup .s4 .v17 .x3),
 .vop (.sub .s4 .v18 .v16 .v17),.vop (.movi0 .v23),.vop (.movi0 .v30),.vop (.movi0 .v31)])) <|
 .seq (CombRound.loop [.x0,.x1,.x2] fun off =>
 [.ldrq .v0 .x1 off,.ldrq .v3 .x0 off,.ldrq .v4 .x2 off] ++ testNorm ++
 [.vop (.add .s4 .v0 .v0 .v3)] ++ CombRound.csub .v0 ++
 [.vop (.sub .s4 .v2 .v17 .v0),.vop (.sub .s4 .v3 .v0 .v18),
 .vop (.logic .and .v2 .v2 .v3),.vop (.shift .sshr .s4 .v2 .v2 31),
 .vop (.cmeq .s4 .v3 .v0 .v18),.vop (.cmeq .s4 .v4 .v4 .v23),
 .vop (.logic .bic .v3 .v3 .v4),.vop (.logic .orr .v2 .v2 .v3),
 .vop (.shift .ushr .s4 .v2 .v2 31),.strq .v2 .x0 off,.vop (.add .s4 .v30 .v30 .v2)]) <|
 .block [.umov .w .x1 .v31 0,.umov .w .x9 .v31 1,.logic .orr .w .x1 .x1 .x9,
 .umov .w .x9 .v31 2,.logic .orr .w .x1 .x1 .x9,.umov .w .x9 .v31 3,.logic .orr .w .x1 .x1 .x9,.addImm .w .x1 .x1 1,
 .umov .w .x0 .v30 0,.umov .w .x9 .v30 1,.add .w .x0 .x0 .x9,
 .umov .w .x9 .v30 2,.add .w .x0 .x0 .x9,.umov .w .x9 .v30 3,.add .w .x0 .x0 .x9,
 .lsl .x .x1 .x1 32,.logic .orr .x .x0 .x0 .x1]
end CombFusedCheck

namespace SquareSignedCheck
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Round
open CombRound
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
 CombFusedCheck.finish
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
 .strq .v0 .x2 off] ++ testNorm) CombFusedCheck.finish
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
end SquareSignedCheck

def main : IO Unit := do
 for (name,p) in [("signed_add_norm",SquareSignedCheck.addNorm),
  ("signed_sub_low_norm",SquareSignedCheck.subLowNorm),("signed_hint_norm",SquareSignedCheck.hintNorm),
  ("signed_canonicalize",SquareSignedCheck.canonicalize),
  ("reference_add_norm",CombFusedCheck.addNorm),("reference_sub_low_norm",CombFusedCheck.subLowNorm),
  ("reference_hint_norm",CombFusedCheck.hintNorm)] do
  let body := printer.function p
  IO.FS.writeFile ("/tmp/square-"++name++".body") (String.join (body.map (Rust.line printer.call)))
  IO.println s!"{name}: {body.length} lines"
