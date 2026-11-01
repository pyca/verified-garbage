module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Gcm.Clmul
public import VerifiedGarbage.Impl.Vector.PPC64LE

/-! # GHASH using POWER8 polynomial multiply

Long inputs use an eight-block loop with powers of H. Adjacent blocks
share both lanes of each polynomial multiply, and all products are XORed
before one reduction. Inputs shorter than sixteen blocks, and the tail,
use the single-block loop. All vector registers are volatile.
-/

@[expose] public section
namespace VG.Impl.Gcm.PPC64LE.Vpmsum
open VG.PPC64LE
open VG.Impl.Gcm.Clmul (poly xInv2Hi)

abbrev Y : VReg := .v0
abbrev C : VReg := .v1
abbrev U : VReg := .v2
abbrev LO : VReg := .v3
abbrev MID : VReg := .v4
abbrev HI : VReg := .v5
abbrev A : VReg := .v6
abbrev T : VReg := .v7
abbrev H : VReg := .v16
abbrev MASK : VReg := .v18
abbrev Z : VReg := .v19

def reverseMask : BitVec 128 := 0x0f0e0d0c0b0a09080706050403020100

export VG.Impl.Vector.PPC64LE (const64)

def pair (d : VReg) (hi lo : Reg) : List Instr :=
  VG.Impl.Vector.PPC64LE.pair d T Z hi lo

def consts : List Instr :=
  [.li .r0 0, .vop (.logic .xor Z Z Z)] ++
  const64 .r8 poly ++ pair C .r8 .r8 ++
  const64 .r8 (reverseMask.extractLsb' 64 64) ++
  const64 .r9 (reverseMask.extractLsb' 0 64) ++ pair MASK .r8 .r9 ++
  const64 .r8 xInv2Hi ++ [.li .r9 3] ++ pair H .r8 .r9

/-- Reverse the 16 loaded bytes: logical low doubleword = first big-endian half. -/
def loadRev (d : VReg) (p : Reg) : List Instr :=
  Impl.Vector.PPC64LE.loadPerm d p MASK

/-- Polynomial product and reduction generators shared with fused ciphers. -/
def productsWith (u lo mid hi zero a key : VReg) : List Instr :=
  [.vop (.sldoi u a zero 8), .vop (.pmsumd hi u key),
   .vop (.sldoi u zero a 8), .vop (.pmsumd lo u key),
   .vop (.pmsumd mid a key)]

def reduceWith (lo mid hi tmp zero poly d : VReg) : List Instr :=
  [.vop (.sldoi tmp lo zero 8), .vop (.pmsumd tmp tmp poly),
   .vop (.sldoi lo lo lo 8), .vop (.logic .xor mid mid lo), .vop (.logic .xor mid mid tmp),
   .vop (.sldoi tmp mid zero 8), .vop (.pmsumd tmp tmp poly),
   .vop (.sldoi hi hi hi 8), .vop (.logic .xor hi hi mid),
   .vop (.sldoi tmp tmp tmp 8), .vop (.logic .xor d hi tmp)]

def products (a key : VReg) : List Instr := productsWith U LO MID HI Z a key

def reduce (d : VReg) : List Instr := reduceWith LO MID HI T Z C d

def mul (d a key : VReg) : List Instr := products a key ++ reduce d

def prologue : List Instr := consts ++ loadRev A .r3 ++ mul H A H ++
  [.vop (.sldoi H H H 8)] ++ loadRev Y .r4

def body : List Instr := loadRev A .r5 ++ [.vop (.logic .xor A A Y)] ++ mul Y A H ++
  [.addi .r5 .r5 16, .subi .r6 .r6 1]

def epilogue : List Instr := [.vop (.perm T Y Y MASK), .stxvd2x T .r4 .r0]

-- H^j / x is stored in the same adjusted layout as the baseline H.
def powerReg : Nat → VReg
 | 1 => H | 2 => .v8 | 3 => .v9 | 4 => .v10
 | 5 => .v11 | 6 => .v12 | 7 => .v13 | _ => .v14

def powerStep (i : Nat) : List Instr :=
  [.vop (.sldoi A (powerReg (i+1)) (powerReg (i+1)) 8)] ++
  mul (powerReg (i+2)) A H ++
  [.vop (.sldoi (powerReg (i+2)) (powerReg (i+2)) (powerReg (i+2)) 8)]

def preparePowers (n : Nat) : List Instr := (List.range (n-1)).flatMap powerStep

-- Pack adjacent blocks' corresponding doublewords so both lanes of each
-- polynomial multiply contribute useful products.
def keyLow : Nat → VReg
 | 0 => .v14 | 1 => .v12 | 2 => .v10 | _ => .v8

def keyHigh : Nat → VReg
 | 0 => .v13 | 1 => .v11 | 2 => .v9 | _ => .v15

def packKeyStep (j : Nat) : List Instr :=
  let a := powerReg (8-2*j)
  let b := powerReg (7-2*j)
  [.vop (.sldoi A b b 8),
   .vop (.sldoi T A a 8), .vop (.sldoi T T T 8),
   .vop (.sldoi (keyLow j) a A 8), .vop (.logic .or (keyHigh j) T T)]

def packedKeys : List Instr := (List.range 4).flatMap packKeyStep

def packedAccs : List (VReg × VReg) := [(Y,LO),(.v16,MID),(.v17,HI)]
def packedProductsWith (a b u t lo mid hi loKey hiKey : VReg) (canonical : Bool) : List Instr :=
  let p := if canonical then t else u
  let q := if canonical then u else t
  [.vop (.sldoi hi b b 8),
   .vop (.sldoi p a hi 8),
   .vop (.sldoi q hi a 8), .vop (.sldoi q q q 8),
   .vop (.pmsumd hi u hiKey), .vop (.pmsumd lo t loKey),
   .vop (.pmsumd mid u loKey), .vop (.pmsumd u t hiKey),
   .vop (.logic .xor mid mid u)]

def packedProducts (loKey hiKey : VReg) : List Instr :=
  packedProductsWith A HI U T LO MID HI loKey hiKey false

def packedSave (j : Nat) : List Instr :=
  if j=0 then packedAccs.map (fun (acc,p) => .vop (.logic .or acc p p))
  else if j=3 then packedAccs.map (fun (acc,p) => .vop (.logic .xor p p acc))
  else packedAccs.map (fun (acc,p) => .vop (.logic .xor acc acc p))

def packedRead (j : Nat) : List Instr :=
  loadRev A .r5 ++ [.addi .r5 .r5 16] ++
  (if j=0 then [.vop (.logic .xor A A Y)] else []) ++
  loadRev HI .r5 ++ [.addi .r5 .r5 16]

def packedPair (j : Nat) : List Instr :=
  packedRead j ++ packedProducts (keyLow j) (keyHigh j) ++ packedSave j

def packedBody : List Instr := (List.range 4).flatMap packedPair ++
  reduce Y ++ [.subi .r6 .r6 8]

def bulk : Prog isa :=
  .seq (.block (preparePowers 8 ++ packedKeys))
    (.seq (.loop (.block (packedBody ++ [.lsr .d .r10 .r6 3])) (.nonzero .d .r10))
      (.block [.vop (.sldoi A (keyLow 3) (keyLow 3) 8), .vop (.sldoi H (keyHigh 3) A 8)]))

def finish : Prog isa :=
  .seq (.ite (.zero .d .r6) (.block []) (.loop (.block body) (.nonzero .d .r6))) (.block epilogue)

/-- Nonempty short messages go directly to the hardware loop. -/
def serial : Prog isa :=
  .seq (.loop (.block body) (.nonzero .d .r6)) (.block epilogue)

def ghash : Prog isa :=
  .ite (.zero .d .r6) (.block [])
    (.seq (.block (prologue ++ [.lsr .d .r10 .r6 4]))
      (.ite (.zero .d .r10) serial (.seq bulk finish)))

end VG.Impl.Gcm.PPC64LE.Vpmsum
