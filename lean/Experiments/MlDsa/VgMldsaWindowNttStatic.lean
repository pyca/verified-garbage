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
 [.vop (.shift .sshr .s4 .v4 d 23),.vop (.mls d .v4 .v16),.vop (.add .s4 d d .v16)]

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
  .seq (.block (movW .x6 8347681 ++
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
  (if up then [] else immediateZ [8347681,8347681,8347681,8347681] ++
    dataRegs.flatMap fun r => fastMul r ++ canon r) ++
  (dataRegs.zipIdx.flatMap fun (r,i) => [.strq r .x2 (128*i)]) ++
  [.addImm .x .x2 .x2 16,.subImm .x .x5 .x5 1])) (.nonzero .x .x5)

def fused3Ntt : Prog isa := .seq (.block fastConsts) <| .seq (fusedOuter true)
 (([16,8,4] : List Nat).foldr (fun len rest => .seq (directLayer true len) rest) (directFused true))
def fused3Inv : Prog isa := .seq (.block fastConsts) <| .seq (directFused false)
 (([4,8,16] : List Nat).foldr (fun len rest => .seq (directLayer false len) rest) (fusedOuter false))


-- Eight packed (root, reciprocal) pairs for the first three layers, initialized once.
def rootRegs : List VReg := [.v25,.v26,.v27,.v28]
def hoistedInit : List Instr :=
 (List.range 4).flatMap fun i =>
  let z0 := zetaTab (2*i+1)
  let z1 := zetaTab (2*i+2)
  constVector rootRegs[i]! [z0,z0*2149582593/2^23,z1,z1*2149582593/2^23]
def hoistedRoot (i : Nat) : List Instr :=
 [.vop (.dupE .s4 .v18 rootRegs[(i-1)/2]! (2*((i-1)%2))),
  .vop (.dupE .s4 .v19 rootRegs[(i-1)/2]! (2*((i-1)%2)+1))]
def outerHoistedOps : List Instr :=
 ([4,2,1] : List Nat).flatMap fun gap =>
  (List.range (4/gap)).flatMap fun group =>
   hoistedRoot (4/gap+group) ++ (List.range gap).flatMap fun j =>
    lazyPair dataRegs[2*gap*group+j]! dataRegs[2*gap*group+j+gap]! true

def outerHoisted : Prog isa :=
 .seq (.block ([mov .x2 .x0,.movz .x .x5 8 0] ++ hoistedInit)) <|
 .loop (.block (
  (dataRegs.zipIdx.flatMap fun (r,i) => [.ldrq r .x2 (128*i)]) ++ outerHoistedOps ++
  (dataRegs.zipIdx.flatMap fun (r,i) => [.strq r .x2 (128*i)]) ++
  [.addImm .x .x2 .x2 16,.subImm .x .x5 .x5 1])) (.nonzero .x .x5)

-- Explicit internal table ABI: x1 has 2048 initialized bytes, one 64-bit pair per index.
def tableSetup : Prog isa := .block <| (List.range 256).flatMap fun i =>
 let z := zetaTab i
 VG.Impl.MlKem.AArch64.movImm .x6 (BitVec.ofNat 64 (z + (z*2149582593/2^23)*2^32)) ++ [.str .x .x6 .x1 (8*i)]
def tableRoot (i : Nat) : List Instr :=
 [.ldr .x .x6 .x1 (8*i),.vop (.dup .d2 .v19 .x6),
  .vop (.dupE .s4 .v18 .v19 0),.vop (.dupE .s4 .v19 .v19 1)]
def root (table : Bool) (i : Nat) : List Instr :=
 if table then tableRoot i else let z := zetaTab i; immediateZ [z,z,z,z]
def packedRoot (table : Bool) (len i : Nat) : List Instr :=
 if table then
  if len=2 then [.ldrq .v19 .x1 (8*i),.vop (.perm .trn1 .s4 .v18 .v19 .v19),.vop (.perm .trn2 .s4 .v19 .v19 .v19)]
  else [.ldrq .v2 .x1 (8*i),.ldrq .v3 .x1 (8*i+16),
   .vop (.perm .uzp1 .s4 .v18 .v2 .v3),.vop (.perm .uzp2 .s4 .v19 .v2 .v3)]
 else let zs := if len=2 then [zetaTab i,zetaTab i,zetaTab (i+1),zetaTab (i+1)]
   else (List.range 4).map fun j => zetaTab (i+j)
      immediateZ zs
-- Temporary vectors25/26/24; all data stay in their eight assigned registers.
def innerPair (a b : VReg) (len : Nat) : List Instr :=
 [ .vop (.perm (if len=2 then .trn1 else .uzp1) (if len=2 then .d2 else .s4) .v25 a b),
   .vop (.perm (if len=2 then .trn2 else .uzp2) (if len=2 then .d2 else .s4) .v26 a b)] ++ fastMul .v26 ++
 [.vop (.sub .s4 .v24 .v25 .v26),.vop (.add .s4 .v25 .v25 .v26),
  .vop (.perm (if len=2 then .trn1 else .zip1) (if len=2 then .d2 else .s4) a .v25 .v24),
  .vop (.perm (if len=2 then .trn2 else .zip2) (if len=2 then .d2 else .s4) b .v25 .v24)]
def innerFive (table : Bool) (block : Nat) : List Instr :=
 (dataRegs.zipIdx.flatMap fun (r,i) => [.ldrq r .x2 (16*i)]) ++
 (([4,2,1] : List Nat).flatMap fun gap =>
   (List.range (4/gap)).flatMap fun g => root table (32/gap + block*(4/gap)+g) ++
    (List.range gap).flatMap fun j => lazyPair dataRegs[2*gap*g+j]! dataRegs[2*gap*g+j+gap]! true) ++
 ((List.range 4).flatMap fun j =>
   packedRoot table 2 (64+8*block+2*j) ++ innerPair dataRegs[2*j]! dataRegs[2*j+1]! 2 ++
   packedRoot table 1 (128+16*block+4*j) ++ innerPair dataRegs[2*j]! dataRegs[2*j+1]! 1) ++
 (dataRegs.flatMap fun r => canon r) ++
 (dataRegs.zipIdx.flatMap fun (r,i) => [.strq r .x2 (16*i)]) ++ [.addImm .x .x2 .x2 128]
def finalFive (table : Bool) : Prog isa :=
 .block ([mov .x2 .x0] ++ (List.range 8).flatMap (innerFive table))
def fusedFive : Prog isa := .seq (.block fastConsts) (.seq outerHoisted (finalFive false))
def fusedFiveCore : Prog isa := .seq (.block fastConsts) (.seq outerHoisted (finalFive true))
-- Internal-only full wrapper: requires2048 scratch bytes, never replaces public1024 ABI directly.
def fusedFiveTable : Prog isa := .seq tableSetup fusedFiveCore
def fusedTwoCore : Prog isa := .seq (.block fastConsts)
 (.seq (layers bfly true [128,64,32,16,8,4]) fusedForward)
def rootOnlySetup : Prog isa := .block (storeTab zetaTab 256 .x1)
def rootAt (base : Reg) (i : Nat) : List Instr :=
 [.ldr .x .x6 base (8*i),.vop (.dup .d2 .v19 .x6),
  .vop (.dupE .s4 .v18 .v19 0),.vop (.dupE .s4 .v19 .v19 1)]
def packedAt (base : Reg) (len i : Nat) : List Instr :=
 if len=2 then [.ldrq .v19 base (8*i),.vop (.perm .trn1 .s4 .v18 .v19 .v19),.vop (.perm .trn2 .s4 .v19 .v19 .v19)]
 else [.ldrq .v2 base (8*i),.ldrq .v3 base (8*i+16),
   .vop (.perm .uzp1 .s4 .v18 .v2 .v3),.vop (.perm .uzp2 .s4 .v19 .v2 .v3)]
def innerFiveLoopBody : List Instr :=
 (dataRegs.zipIdx.flatMap fun (r,i) => [.ldrq r .x2 (16*i)]) ++
 (([4,2,1] : List Nat).flatMap fun gap =>
   (List.range (4/gap)).flatMap fun g => rootAt (if gap=4 then .x3 else if gap=2 then .x4 else .x5) g ++
    (List.range gap).flatMap fun j => lazyPair dataRegs[2*gap*g+j]! dataRegs[2*gap*g+j+gap]! true) ++
 ((List.range 4).flatMap fun j =>
   packedAt .x7 2 (2*j) ++ innerPair dataRegs[2*j]! dataRegs[2*j+1]! 2 ++
   packedAt .x8 1 (4*j) ++ innerPair dataRegs[2*j]! dataRegs[2*j+1]! 1) ++
 (dataRegs.flatMap fun r => canon r) ++
 (dataRegs.zipIdx.flatMap fun (r,i) => [.strq r .x2 (16*i)]) ++
 [.addImm .x .x2 .x2 128,.addImm .x .x3 .x3 8,.addImm .x .x4 .x4 16,
  .addImm .x .x5 .x5 32,.addImm .x .x7 .x7 64,.addImm .x .x8 .x8 128,.subImm .x .x10 .x10 1]
def finalFiveLoop : Prog isa :=
 .seq (.block [mov .x2 .x0,.addImm .x .x3 .x1 64,.addImm .x .x4 .x1 128,.addImm .x .x5 .x1 256,
  .addImm .x .x7 .x1 512,.addImm .x .x8 .x1 1024,.movz .x .x10 8 0])
 (.loop (.block innerFiveLoopBody) (.nonzero .x .x10))
def fusedFiveLoopCore : Prog isa := .seq (.block fastConsts) (.seq outerHoisted finalFiveLoop)
def fusedFiveLoopTable : Prog isa := .seq tableSetup fusedFiveLoopCore
structure Ren where
 code : List Instr := []
 data : List VReg := dataRegs
 free : VReg := .v24

def prodTemps : List VReg := [.v4,.v29,.v30,.v31]
def renGroup (r : Ren) (gap group : Nat) (roots : List Instr) : Ren :=
 let bs := (List.range gap).map fun j => r.data[2*gap*group+j+gap]!
 let ops := ((bs.zipIdx).map fun (b,i) => .vop (.sqdmulh prodTemps[i]! b .v19)) ++
  (bs.map fun b => .vop (.mul b b .v18)) ++
  ((bs.zipIdx).map fun (b,i) => .vop (.mls b prodTemps[i]! .v16))
 (List.range gap).foldl (fun st j =>
   let a := st.data[2*gap*group+j]!
   let b := st.data[2*gap*group+j+gap]!
   { code := st.code ++ [.vop (.sub .s4 st.free a b),.vop (.add .s4 a a b)]
     data := st.data.set (2*gap*group+j+gap) st.free
     free := b }) {r with code := r.code ++ roots ++ ops}
def renThree (outer table : Bool) (block : Nat) : Ren :=
 ([4,2,1] : List Nat).foldl (fun st gap =>
  (List.range (4/gap)).foldl (fun st g =>
   let rs := if outer then hoistedRoot (4/gap+g)
    else if table then rootAt (if gap=4 then .x3 else if gap=2 then .x4 else .x5) g
    else root false (32/gap+block*(4/gap)+g)
   renGroup st gap g rs) st) {}
def outerRenamed : Prog isa :=
 let r := renThree true false 0
 .seq (.block ([mov .x2 .x0,.movz .x .x5 8 0] ++ hoistedInit)) <|
 .loop (.block (
  (dataRegs.zipIdx.flatMap fun (v,i) => [.ldrq v .x2 (128*i)]) ++ r.code ++
  (r.data.zipIdx.flatMap fun (v,i) => [.strq v .x2 (128*i)]) ++
  [.addImm .x .x2 .x2 16,.subImm .x .x5 .x5 1])) (.nonzero .x .x5)
def renInnerPair (a b tmp : VReg) (len : Nat) : List Instr :=
 [ .vop (.perm (if len=2 then .trn1 else .uzp1) (if len=2 then .d2 else .s4) .v25 a b),
   .vop (.perm (if len=2 then .trn2 else .uzp2) (if len=2 then .d2 else .s4) .v26 a b)] ++ fastMul .v26 ++
 [.vop (.sub .s4 tmp .v25 .v26),.vop (.add .s4 .v25 .v25 .v26),
  .vop (.perm (if len=2 then .trn1 else .zip1) (if len=2 then .d2 else .s4) a .v25 tmp),
  .vop (.perm (if len=2 then .trn2 else .zip2) (if len=2 then .d2 else .s4) b .v25 tmp)]
def renFiveBody (table canonical : Bool) (block : Nat) : List Instr :=
 let r := renThree false table block
 (dataRegs.zipIdx.flatMap fun (v,i) => [.ldrq v .x2 (16*i)]) ++ r.code ++
 ((List.range 4).flatMap fun j =>
   (if table then packedAt .x7 2 (2*j) else packedRoot false 2 (64+8*block+2*j)) ++
    renInnerPair r.data[2*j]! r.data[2*j+1]! r.free 2 ++
   (if table then packedAt .x8 1 (4*j) else packedRoot false 1 (128+16*block+4*j)) ++
    renInnerPair r.data[2*j]! r.data[2*j+1]! r.free 1) ++
 (if canonical then r.data.flatMap fun v => canon v else []) ++
 (r.data.zipIdx.flatMap fun (v,i) => [.strq v .x2 (16*i)]) ++ [.addImm .x .x2 .x2 128]
def renFive (table canonical : Bool) : Prog isa :=
 if table then
  .seq (.block [mov .x2 .x0,.addImm .x .x3 .x1 64,.addImm .x .x4 .x1 128,.addImm .x .x5 .x1 256,
   .addImm .x .x7 .x1 512,.addImm .x .x8 .x1 1024,.movz .x .x10 8 0])
  (.loop (.block (renFiveBody true canonical 0 ++ [.addImm .x .x3 .x3 8,.addImm .x .x4 .x4 16,
   .addImm .x .x5 .x5 32,.addImm .x .x7 .x7 64,.addImm .x .x8 .x8 128,.subImm .x .x10 .x10 1])) (.nonzero .x .x10))
 else .block ([mov .x2 .x0] ++ (List.range 8).flatMap (renFiveBody false canonical))
def renamedNtt (table canonical : Bool) : Prog isa :=
 .seq (.block fastConsts) (.seq outerRenamed (renFive table canonical))
end WindowFusedNtt

def staticNttWords : List (BitVec 64) := (List.range 256).map fun i =>
 let z := WindowFusedNtt.zetaTab i
 BitVec.ofNat 64 (z + (z*2149582593/2^23)*2^32)
def staticNtt : Prog isa := .seq (.block [.adrSym .x1 "MLDSA_NTT_BARRETT"])
 (WindowFusedNtt.renamedNtt true true)
def main : IO Unit := do
 let lines := printer.function staticNtt
 IO.FS.writeFile "/tmp/vg-window-ntt-static-positive.body"
  (String.join (lines.map (Rust.line printer.call)) ++ "        MLDSA_NTT_BARRETT = sym super::consts::MLDSA_NTT_BARRETT,\n")
 IO.FS.writeFile "/tmp/vg-window-ntt-static-consts.rs"
  (Rust.tablesFile "aarch64" [("MLDSA_NTT_BARRETT",staticNttWords)])
 IO.FS.writeFile "/tmp/vg-window-ntt-static-sym-macros.rs" Rust.symMacros
 IO.FS.writeFile "/tmp/vg-window-ntt-static-metadata.txt"
  "symbol=MLDSA_NTT_BARRETT\nwords=256\nbytes=2048\nalignment=64\nlayout=zeta_i|(bar_i<<32)\noutput=positive_less_than_3q\nscratch=unused\n"
