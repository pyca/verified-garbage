module

public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.AArch64

/-!
# Joint radix-four Brainpool P-512 verification on AArch64

The verification scalars are public. A table of the fifteen nonzero digit pairs
`[i]G + [j]Q`, `0 ≤ i,j < 4`, permits one shared chain of 512 doublings and at
most 256 additions, instead of two complete 512-bit double-and-add ladders.
The complete general RCB formulas handle equal and opposite points and infinity.
Neither secret-scalar multiplication nor signing uses this public lookup.

The two 512-byte bit tables occupy bytes 2944–3967; the Montgomery helper owns
3968–4095. Fifteen projective triples occupy 5280–8159. All arithmetic uses the
existing low slots, so a helper call never overlaps the lookup tables.
-/

@[expose] public section
namespace VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V UX UY UZ)

abbrev cfg := brainpoolp512r1
abbrev resultPt : Pt := cfg.pt RX RY RZ
abbrev entry : Pt := cfg.pt UX UY UZ
abbrev bitsU : Nat := 2944
abbrev bitsV : Nat := 3456
abbrev tableAt : Nat := 5280

/-- Digit pair `i + 4j`, numbered from one. There is no stored zero entry. -/
def tablePt (d : Nat) : Pt :=
  ⟨tableAt + 192 * (d-1),tableAt + 192 * (d-1) + 64,tableAt + 192 * (d-1) + 128⟩

def infinity : List Instr :=
  setConst 8 resultPt.x 0 ++ setConst 8 resultPt.y (cfg.mont 1) ++ setConst 8 resultPt.z 0

def affineEntry (x y : Nat) : List Instr :=
  copy 8 entry.x (cfg.sl x) ++ copy 8 entry.y (cfg.sl y) ++ copy 8 entry.z (cfg.sl ONEP)

def addPoints : Prog isa := sum cfg

/-- The previous digit pair, plus `G`, or the previous row's first pair plus `Q`. -/
def tableStep (d : Nat) : Prog isa :=
  let previous := if d % 4 = 0 then d-4 else d-1
  let source := if previous = 0 then infinity else copyPt 8 resultPt (tablePt previous)
  let (x,y) := if d % 4 = 0 then (PX,PY) else (GX,GY)
  .seq (.block (source ++ affineEntry x y)) <|
  .seq addPoints (.block (copyPt 8 (tablePt d) resultPt))

def build : Nat → Prog isa
  | 0 => .block []
  | m+1 => .seq (build m) (tableStep (m+1))

def double : Prog isa := .seq (.block (copyPt 8 entry resultPt)) addPoints

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
  [.subImm .x .x2 .x2 1,.movz .x .x17 192 0,.mul .x .x2 .x2 .x17,
   .movz .x .x16 tableAt 0,.add .x .x16 .x0 .x16,.add .x .x16 .x16 .x2]

def fetch : List Instr :=
  fetchHead ++ copyFrom 8 entry.x 0 ++ copyFrom 8 entry.y 64 ++ copyFrom 8 entry.z 128

def digitTail : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.seq (.block fetch) addPoints)

def addDigit : Prog isa := .seq (.block digit) digitTail

def stepFront : Prog isa :=
  .seq (.block [decCounter]) (.seq double (.seq double (.block digit)))

def step : Prog isa :=
  .seq (.block [decCounter]) (.seq double (.seq double addDigit))

def prepare : Prog isa :=
  .seq (bits (cfg.sl U) bitsU 64) <|
  .seq (bits (cfg.sl V) bitsV 64)
    (.block (setConst 8 (cfg.sl EXPP) (cfg.mont (3 * cfg.C.b))))

def setup : Prog isa :=
  .seq prepare <| .seq (build 15) (.block (infinity ++ [.movz .x .x19 256 0]))

def points : Prog isa :=
  .seq setup (.loop step (.nonzero .x .x19))

def verify : Prog isa := verifyWithPoints cfg points
end VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint
