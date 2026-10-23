module

public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.AArch64

/-!
# Joint radix-four brainpoolp384r1 verification on AArch64

The verification scalars are public. A table of the fifteen nonzero digit pairs
`[i]G + [j]Q`, `0 ≤ i,j < 4`, permits one shared chain of 384 doublings and at
most 192 additions, instead of two complete 384-bit double-and-add ladders.
The complete general RCB formulas handle equal and opposite points and infinity.
Neither secret-scalar multiplication nor signing uses this public lookup.

The two 384-byte bit tables occupy bytes 2944–3711. Fifteen projective triples occupy 5280–7439. All arithmetic uses the
existing low slots, so a helper call never overlaps the lookup tables.
-/

@[expose] public section
namespace VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V UX UY UZ)

abbrev cfg := brainpoolp384r1
abbrev resultPt : Pt := cfg.pt RX RY RZ
abbrev entry : Pt := cfg.pt UX UY UZ
abbrev bitsU : Nat := 2944
abbrev bitsV : Nat := 3328
abbrev tableAt : Nat := 5280

/-- Digit pair `i + 4j`, numbered from one. There is no stored zero entry. -/
def tablePt (d : Nat) : Pt :=
  ⟨tableAt + 144 * (d-1),tableAt + 144 * (d-1) + 48,tableAt + 144 * (d-1) + 96⟩

def infinity : List Instr :=
  setConst 6 resultPt.x 0 ++ setConst 6 resultPt.y (cfg.mont 1) ++ setConst 6 resultPt.z 0

def affineEntry (x y : Nat) : List Instr :=
  copy 6 entry.x (cfg.sl x) ++ copy 6 entry.y (cfg.sl y) ++ copy 6 entry.z (cfg.sl ONEP)

def addPoints : Prog isa := sum cfg

def double : Prog isa := .seq (.block (copyPt 6 entry resultPt)) addPoints

/-- The digit pair `u[2j:2j+2] + 4 v[2j:2j+2]` in `x2`. -/
def digit : List Instr :=
  [.lsl .x .x16 .x19 1,.add .x .x16 .x0 .x16] ++
  hornerBits bitsU 2 ++ [.addImm .x .x6 .x2 0] ++ hornerBits bitsV 2 ++
  [.lsl .x .x2 .x2 2,.add .x .x2 .x2 .x6]

/-- Copy `n` words from the selected entry pointer into a coordinate. -/
def copyFrom : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | n+1, dst, src => [.ldr .x .x4 .x16 src,st .x4 dst] ++ copyFrom n (dst+8) (src+8)

/-- Load a nonzero public digit pair into the addition's three input slots. -/
def fetchHead : List Instr :=
  [.subImm .x .x2 .x2 1,.movz .x .x17 144 0,.mul .x .x2 .x2 .x17,
   .movz .x .x16 tableAt 0,.add .x .x16 .x0 .x16,.add .x .x16 .x16 .x2]

def fetch : List Instr :=
  fetchHead ++ copyFrom 6 entry.x 0 ++ copyFrom 6 entry.y 48 ++ copyFrom 6 entry.z 96

def digitTail : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.seq (.block fetch) addPoints)

def addDigit : Prog isa := .seq (.block digit) digitTail

def stepFront : Prog isa :=
  .seq (.block [decCounter]) (.seq double (.seq double (.block digit)))

def step : Prog isa :=
  .seq (.block [decCounter]) (.seq double (.seq double addDigit))

def prepare : Prog isa :=
  .seq (bits (cfg.sl U) bitsU 48) <|
  .seq (bits (cfg.sl V) bitsV 48)
    (.block (setConst 6 (cfg.sl EXPP) (cfg.mont (3 * cfg.C.b))))

/-- Select one of fifteen short copy paths using the public table counter. -/
def choose (f : Nat → Prog isa) : Nat → Prog isa
  | 0 => .block []
  | m+1 => .seq (.block [.subImm .x .x2 .x19 (m+1)])
      (.ite (.zero .x .x2) (f (m+1)) (choose f m))

def tablePrep (d : Nat) : Prog isa :=
  let previous := if d % 4 = 0 then d-4 else d-1
  let source := if previous = 0 then infinity else copyPt 6 resultPt (tablePt previous)
  let (x,y) := if d % 4 = 0 then (PX,PY) else (GX,GY)
  .block (source ++ affineEntry x y)

def tableStore (d : Nat) : Prog isa := .block (copyPt 6 (tablePt d) resultPt)

def prepChoice : Prog isa := choose tablePrep 15
def storeChoice : Prog isa := choose tableStore 15

/-- One shared complete addition serves every table entry. -/
def tableLoopStep : Prog isa :=
  .seq prepChoice <| .seq addPoints <| .seq storeChoice
    (.block [.addImm .x .x19 .x19 1,.subImm .x .x6 .x19 16])

def buildTable : Prog isa :=
  .seq (.block [.movz .x .x19 1 0]) (.loop tableLoopStep (.nonzero .x .x6))

def setup : Prog isa :=
  .seq prepare <| .seq buildTable (.block (infinity ++ [.movz .x .x19 192 0]))

def points : Prog isa := .seq setup (.loop step (.nonzero .x .x19))

def verify : Prog isa := verifyWithPoints cfg points
end VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
