module

public import VerifiedGarbage.Impl.MlKem.AArch64.Sample
public import VerifiedGarbage.Impl.MlKem.AArch64.Lay

/-! # Eight-candidate rejection sampling for AArch64 ML-KEM

The vector step consumes twelve stream bytes and writes at most eight
canonical coefficients. It executes only with room for all eight stores;
the final coefficients use the scalar parser. The table index depends only
on the public matrix seed. A caller provides four readable padding bytes
following the stream and must clear any unwritten suffix on failure.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Impl.MlKem.AArch64

def maskVec (v : VReg) (xs : List Nat) : List Instr :=
 let word (start : Nat) := (List.range 8).foldl (fun a i => a + (xs.getD (start+i) 255)*2^(8*i)) 0
 movImm .x9 (BitVec.ofNat 64 (word 0)) ++ [.vop (.dup .d2 v .x9)] ++
 movImm .x9 (BitVec.ofNat 64 (word 8)) ++ [.vop (.ins .d2 v 1 .x9)]
/-- Increasing indices of the candidates accepted by an eight-bit mask. -/
def acceptedLanes (mask : Nat) : List Nat :=
  (List.range 8).filter (fun i => (mask / 2^i)%2 == 1)

/-- Two byte indices for each accepted halfword, with TBL's zero index for
unused lanes. -/
def tableRow (mask : Nat) : List Nat :=
  (acceptedLanes mask).flatMap fun i => [2*i,2*i+1]

/-- One of the two words of a shuffle-table entry. -/
def tableWord (mask j : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 8).foldl
    (fun n i => n+(tableRow mask |>.getD (8*j+i) 255)*2^(8*i)) 0)

def tableWords : List (BitVec 64) :=
  (List.range 256).flatMap fun mask => (List.range 2).map (tableWord mask)
def rejConsts : List Instr :=
 maskVec .v16 [0,1,2,255,3,4,5,255,6,7,8,255,9,10,11,255] ++
 maskVec .v17 [255,15,0,0,255,15,0,0,255,15,0,0,255,15,0,0] ++
 maskVec .v20 [1,1,2,1,4,1,8,1,16,1,32,1,64,1,128,1] ++
 [.movz .x .x9 3329 0,.vop (.dup .h8 .v19 .x9),.vop (.movi0 .v21),
 .movz .x .x9 0 0,.str .x .x9 .x19 1408,.adrSym .x16 "VG_MLKEM_REJ_SHUFFLE"]
/-- Decode twelve bytes into eight 12-bit halfwords. -/
def parse : List Instr :=
 [.ldrq .v0 .x2 0,.vop (.tbl .v0 .v0 .v16),.vop (.shift .ushr .s4 .v1 .v0 12),
 .vop (.logic .and .v0 .v0 .v17),.vop (.perm .uzp1 .h8 .v0 .v0 .v0),
 .vop (.perm .uzp1 .h8 .v1 .v1 .v1),.vop (.perm .zip1 .h8 .v0 .v0 .v1)]

/-- Each accepted lane contributes its bit position and one count. -/
def accept : List Instr :=
 [.vop (.sub .h8 .v1 .v0 .v19),.vop (.shift .ushr .h8 .v1 .v1 15),
 .vop (.mulH .mul .v1 .v1 .v20)]

/-- Sum the lane weights, then compact according to the low-byte mask. -/
def compact (w16 : Bool := false) : List Instr :=
 [.vop (.ext .v2 .v1 .v1 8),.vop (.add .h8 .v1 .v1 .v2),
 .vop (.ext .v2 .v1 .v1 4),.vop (.add .h8 .v1 .v1 .v2),
 .vop (.ext .v2 .v1 .v1 2),.vop (.add .h8 .v1 .v1 .v2),.umov .w .x6 .v1 0,
 .movz .x .x7 255 0,.logic .and .x .x7 .x6 .x7,.lsl .x .x7 .x7 4,.add .x .x7 .x16 .x7,
 .ldrq .v2 .x7 0,.vop (.tbl .v0 .v0 .v2)] ++
 (if w16 then [.strq .v0 .x3 0] else [.vop (.perm .zip1 .h8 .v1 .v0 .v21),
 .vop (.perm .zip2 .h8 .v2 .v0 .v21),.strq .v1 .x3 0,.strq .v2 .x3 16]) ++
 [.lsr .x .x6 .x6 8,.movz .x .x7 15 0,.logic .and .x .x6 .x6 .x7,
 .sub .x .x4 .x4 .x6,.lsl .x .x6 .x6 (if w16 then 1 else 2),.add .x .x3 .x3 .x6,
 .addImm .x .x2 .x2 12,.subImm .x .x5 .x5 4]

def rejEight (w16 : Bool := false) : List Instr := parse ++ accept ++ compact w16
def rejLoop (w16 : Bool := false) : Prog isa :=
 .seq (.loop (.seq (.block [.subImm .x .x6 .x4 8,.lsr .x .x6 .x6 63])
  (.ite (.zero .x .x6) (.block (rejEight w16)) (.seq (seqs [sampleBody w16,sampleBody w16,sampleBody w16,sampleBody w16])
   (.ite (.zero .x .x4) (.block [.movz .x .x5 0 0]) (.block []))))) (.nonzero .x .x5))
 (.seq (.ite (.zero .x .x4) (.block []) (.block [.movz .x .x13 0 0,.str .w .x13 .x3 0]))
 (.block [.subImm .x .x0 .x4 1,.lsr .x .x0 .x0 63]))

end VG.Impl.MlKem.AArch64.Rej8
