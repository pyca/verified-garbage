import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith
open VG.Impl.MlDsa.AArch64.Arith.Neon

namespace WindowFusedNtt
open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Arith (storeTab movW)


def bbar : List Instr :=
 [.vop (.umull false .v2 .v18 .v20),.vop (.umull true .v3 .v18 .v20),
 .vop (.shift .ushr .d2 .v2 .v2 23),.vop (.shift .ushr .d2 .v3 .v3 23),
 .vop (.perm .uzp1 .s4 .v19 .v2 .v3)]
def fastMul (d : VReg) : List Instr :=
 [.vop (.sqdmulh .v4 d .v19),.vop (.mul d d .v18),.vop (.mls d .v4 .v16)]
def fastConsts : List Instr :=
 Neon.consts ++ movW .x9 2149582593 ++ [.vop (.dup .s4 .v20 .x9)]
def canon (d : VReg) : List Instr :=
 [.vop (.shift .sshr .s4 .v4 d 23),.vop (.mls d .v4 .v16),
  .vop (.shift .sshr .s4 .v4 d 31),.vop (.logic .and .v4 .v4 .v16),
  .vop (.add .s4 d d .v4)] ++ Neon.csub d .v4

def bfly : List Instr := fastMul .v1 ++
 [.vop (.sub .s4 .v5 .v0 .v1),.vop (.add .s4 .v0 .v0 .v1)]
def bflyInv : List Instr :=
 [.vop (.sub .s4 .v5 .v0 .v1),.vop (.add .s4 .v0 .v0 .v1)] ++ fastMul .v5

def zetaTab (m : Nat) : Nat := 1753 ^ Spec.MlDsa.bitRev8 m % 8380417

def negZetaTab (m : Nat) : Nat :=
  ((8380417 - 1753 ^ Spec.MlDsa.bitRev8 m % 8380417) % 8380417) % 8380417

def stepZ (up : Bool) : Instr :=
  if up then .addImm .x .x3 .x3 4 else .subImm .x .x3 .x3 4

/-- Arrange two or four block zetas in butterfly lane order. -/
def zetaPerms (len : Nat) (up : Bool) : List Instr :=
  (if len = 2 then [.vop (.perm .zip1 .s4 .v18 .v18 .v18)] else []) ++
    if up then [] else
      (if len = 1 then [.vop (.rev .rev64s .v18 .v18)] else []) ++ [.vop (.ext .v18 .v18 .v18 8)]

def packedZetas (len : Nat) (up : Bool) : List Instr :=
  (if up then [] else [.subImm .x .x3 .x3 (4*(4/len-1))]) ++
  [.ldrq .v18 .x3 0] ++ zetaPerms len up ++
  [if up then .addImm .x .x3 .x3 (16/len) else .subImm .x .x3 .x3 4]

/-- Load one zeta per block, replicated across its lanes. -/
def rawZetas (len : Nat) (up : Bool) : List Instr :=
  if len = 2 then packedZetas len up
  else if len = 1 then packedZetas len up
  else [.ldr .w .x6 .x3 0, stepZ up, .vop (.dup .s4 .v18 .x6)]

def zetas (len : Nat) (up : Bool) : List Instr := rawZetas len up ++ bbar

def body (bf : List Instr) (len : Nat) : List Instr :=
  [.ldrq .v0 .x2 0, .ldrq .v1 .x2 (4*len)] ++ bf ++
  [.strq .v0 .x2 0, .strq .v5 .x2 (4*len), .addImm .x .x2 .x2 16, .subImm .x .x5 .x5 1]

def block (bf : List Instr) (len : Nat) (up : Bool) : Prog isa :=
  .seq (.block (zetas len up ++ [.movz .x .x5 (BitVec.ofNat 16 (len/4)) 0]))
    (.seq (.loop (.block (body bf len)) (.nonzero .x .x5))
      (.block [.addImm .x .x2 .x2 (4*len), .subImm .x .x4 .x4 1]))

def gather (len : Nat) : List Instr :=
  if len = 2 then
    [.vop (.perm .trn1 .d2 .v0 .v6 .v7), .vop (.perm .trn2 .d2 .v1 .v6 .v7)]
  else [.vop (.perm .uzp1 .s4 .v0 .v6 .v7), .vop (.perm .uzp2 .s4 .v1 .v6 .v7)]

def scatter (len : Nat) : List Instr :=
  if len = 2 then
    [.vop (.perm .trn1 .d2 .v6 .v0 .v5), .vop (.perm .trn2 .d2 .v7 .v0 .v5)]
  else [.vop (.perm .zip1 .s4 .v6 .v0 .v5), .vop (.perm .zip2 .s4 .v7 .v0 .v5)]

def packedBody (bf : List Instr) (len : Nat) (up : Bool) : List Instr :=
  [.ldrq .v6 .x2 0, .ldrq .v7 .x2 16] ++ zetas len up ++ gather len ++ bf ++ scatter len ++
  [.strq .v6 .x2 0, .strq .v7 .x2 16, .addImm .x .x2 .x2 32, .subImm .x .x5 .x5 1]

/-- The zeta range of a layer is known statically. -/
def layer (bf : List Instr) (len : Nat) (up : Bool) : Prog isa :=
  .seq (.block [mov .x2 .x0, .addImm .x .x3 .x1 (4*(if up then 128/len else 256/len-1))])
    (if len < 4 then
      .seq (.block [.movz .x .x5 32 0])
        (.loop (.block (packedBody bf len up)) (.nonzero .x .x5))
     else .seq (.block [.movz .x .x4 (BitVec.ofNat 16 (128/len)) 0])
       (.loop (block bf len up) (.nonzero .x .x4)))

def layers (bf : List Instr) (up : Bool) : List Nat → Prog isa
  | [] => .block []
  | len :: lens => .seq (layer bf len up) (layers bf up lens)

def pro (tab : Nat → Nat) : List Instr := storeTab tab 256 .x1 ++ fastConsts

def finish : Prog isa :=
 .seq (.block [mov .x2 .x0,.movz .x .x5 64 0])
 (.loop (.block ([.ldrq .v0 .x2 0] ++ canon .v0 ++
 [.strq .v0 .x2 0,.addImm .x .x2 .x2 16,.subImm .x .x5 .x5 1])) (.nonzero .x .x5))
def fusedForwardBody : List Instr :=
 [.ldrq .v6 .x2 0,.ldrq .v7 .x2 16] ++
 zetas 2 true ++ gather 2 ++ bfly ++ scatter 2 ++
 [.ldrq .v18 .x7 0,.addImm .x .x7 .x7 16] ++ bbar ++
 gather 1 ++ bfly ++ scatter 1 ++ canon .v6 ++ canon .v7 ++
 [.strq .v6 .x2 0,.strq .v7 .x2 16,.addImm .x .x2 .x2 32,.subImm .x .x5 .x5 1]
def fusedForward : Prog isa :=
 .seq (.block [mov .x2 .x0,.addImm .x .x3 .x1 256,.addImm .x .x7 .x1 512,.movz .x .x5 32 0])
 (.loop (.block fusedForwardBody) (.nonzero .x .x5))
def ntt : Prog isa := .seq (.block (pro zetaTab))
 (.seq (layers bfly true [128,64,32,16,8,4]) fusedForward)

def swapZ : List Instr := [mov .x6 .x3,mov .x3 .x7,mov .x7 .x6]
def fusedInverseBody : List Instr :=
 [.ldrq .v6 .x2 0,.ldrq .v7 .x2 16] ++
 zetas 1 false ++ gather 1 ++ bflyInv ++ scatter 1 ++
 swapZ ++ zetas 2 false ++ swapZ ++ gather 2 ++ bflyInv ++ scatter 2 ++
 [.strq .v6 .x2 0,.strq .v7 .x2 16,.addImm .x .x2 .x2 32,.subImm .x .x5 .x5 1]
def fusedInverse : Prog isa :=
 .seq (.block [mov .x2 .x0,.addImm .x .x3 .x1 1020,.addImm .x .x7 .x1 508,.movz .x .x5 32 0])
 (.loop (.block fusedInverseBody) (.nonzero .x .x5))

def scaleBody : List Instr :=
  [.ldrq .v0 .x2 0] ++ fastMul .v0 ++ canon .v0 ++
    [.strq .v0 .x2 0, .addImm .x .x2 .x2 16, .subImm .x .x5 .x5 1]

def scale : Prog isa :=
  .seq (.block (movW .x6 16382 ++
    [.vop (.dup .s4 .v18 .x6), mov .x2 .x0, .movz .x .x5 64 0] ++ bbar))
    (.loop (.block scaleBody) (.nonzero .x .x5))

def nttInv : Prog isa := .seq (.block (pro negZetaTab))
  (.seq fusedInverse (.seq (layers bflyInv false [4,8,16,32,64,128]) scale))

def constVector (d : VReg) (xs : List Nat) : List Instr :=
 movW .x6 xs[0]! ++ [.vop (.dup .s4 d .x6)] ++
 ((List.range 3).flatMap fun i =>
  if xs[i+1]! = xs[0]! then [] else movW .x6 xs[i+1]! ++ [.vop (.ins .s4 d (i+1) .x6)])
def immediateZ (xs : List Nat) : List Instr :=
 constVector .v18 xs ++ constVector .v19 (xs.map fun z => z*2149582593/2^23)
def directBlock (up : Bool) (len index : Nat) : Prog isa :=
 let z := if up then zetaTab index else negZetaTab index
 .seq (.block (immediateZ [z,z,z,z] ++ [.movz .x .x5 (BitVec.ofNat 16 (len/4)) 0]))
 (.seq (.loop (.block (body (if up then bfly else bflyInv) len)) (.nonzero .x .x5))
 (.block [.addImm .x .x2 .x2 (4*len)]))
def directLayer (up : Bool) (len : Nat) : Prog isa :=
 .seq (.block [mov .x2 .x0])
 ((List.range (128/len)).foldr (fun g tail =>
  .seq (directBlock up len (if up then 128/len+g else 256/len-1-g)) tail) (.block []))
def directFusedBody (up : Bool) (i : Nat) : List Instr :=
 let z2 := if up then [zetaTab (64+2*i),zetaTab (64+2*i),zetaTab (65+2*i),zetaTab (65+2*i)]
   else [negZetaTab (127-2*i),negZetaTab (127-2*i),negZetaTab (126-2*i),negZetaTab (126-2*i)]
 let z1 := (List.range 4).map fun j => if up then zetaTab (128+4*i+j) else negZetaTab (255-4*i-j)
 [.ldrq .v6 .x2 0,.ldrq .v7 .x2 16] ++
 (if up then immediateZ z2 ++ gather 2 ++ bfly ++ scatter 2 ++
    immediateZ z1 ++ gather 1 ++ bfly ++ scatter 1 ++ canon .v6 ++ canon .v7
 else immediateZ z1 ++ gather 1 ++ bflyInv ++ scatter 1 ++
    immediateZ z2 ++ gather 2 ++ bflyInv ++ scatter 2) ++
 [.strq .v6 .x2 0,.strq .v7 .x2 16,.addImm .x .x2 .x2 32]
def directFused (up : Bool) : Prog isa :=
 .block ([mov .x2 .x0] ++ (List.range 32).flatMap (directFusedBody up))
def directNtt : Prog isa := .seq (.block fastConsts)
 (([128,64,32,16,8,4] : List Nat).foldr (fun len rest => .seq (directLayer true len) rest) (directFused true))
def directInv : Prog isa := .seq (.block fastConsts) <| .seq (directFused false)
 (([4,8,16,32,64,128] : List Nat).foldr (fun len rest => .seq (directLayer false len) rest) scale)

def dataRegs : List VReg := [.v0,.v1,.v5,.v6,.v7,.v21,.v22,.v23]
def lazyPair (a b : VReg) (up : Bool) : List Instr :=
 if up then fastMul b ++
  [.vop (.sub .s4 .v24 a b),.vop (.add .s4 a a b),.vop (.mov b .v24)]
 else [.vop (.sub .s4 .v24 a b),.vop (.add .s4 a a b),.vop (.mov b .v24)] ++ fastMul b

def fusedOuterOps (up : Bool) : List Instr :=
 ((if up then [4,2,1] else [1,2,4]) : List Nat).flatMap fun gap =>
  (List.range (4/gap)).flatMap fun group =>
   let z := if up then zetaTab (4/gap+group) else negZetaTab (8/gap-1-group)
   immediateZ [z,z,z,z] ++ (List.range gap).flatMap fun j =>
    lazyPair dataRegs[2*gap*group+j]! dataRegs[2*gap*group+j+gap]! up

def fusedOuter (up : Bool) : Prog isa :=
 .seq (.block [mov .x2 .x0,.movz .x .x5 8 0]) <|
 .loop (.block (
  (dataRegs.zipIdx.flatMap fun (r,i) => [.ldrq r .x2 (128*i)]) ++ fusedOuterOps up ++
  (if up then [] else immediateZ [16382,16382,16382,16382] ++
    dataRegs.flatMap fun r => fastMul r ++ canon r) ++
  (dataRegs.zipIdx.flatMap fun (r,i) => [.strq r .x2 (128*i)]) ++
  [.addImm .x .x2 .x2 16,.subImm .x .x5 .x5 1])) (.nonzero .x .x5)

def fused3Ntt : Prog isa := .seq (.block fastConsts) <| .seq (fusedOuter true)
 (([16,8,4] : List Nat).foldr (fun len rest => .seq (directLayer true len) rest) (directFused true))
def fused3Inv : Prog isa := .seq (.block fastConsts) <| .seq (directFused false)
 (([4,8,16] : List Nat).foldr (fun len rest => .seq (directLayer false len) rest) (fusedOuter false))
end WindowFusedNtt

def main : IO Unit := do
 for (name,code) in [("inv_ntt",WindowFusedNtt.fused3Inv)] do
  IO.FS.writeFile ("/tmp/vg-mldsa-window-fused3-mont-"++name++".body") (String.join ((printer.function code).map (Rust.line printer.call)))
