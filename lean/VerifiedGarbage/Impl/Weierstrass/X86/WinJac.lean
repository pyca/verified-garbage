import VerifiedGarbage.Impl.Weierstrass.X86.Naf
import VerifiedGarbage.Impl.Weierstrass.X86.CachedJac
import VerifiedGarbage.Impl.Weierstrass.JacMul

/-! Constant-time five-bit variable-base multiplication on 32-bit x86.

The accumulator stays Jacobian until the final conversion. The table has
16 Jacobian points followed by their cached Z² and Z³ coordinates. Two
SSE2 scans read every entry for each secret digit. The field operations
use only low scratch slots; the table may lie above the field workspace.
-/
namespace VG.Impl.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass

structure JacWinCfg where
  M : Mod
  F : Spec.Weierstrass.Mont.Modulus
  S : RcbSlots
  P : Pt
  R : Pt
  D : Pt
  T : Nat
  neg : Nat
  zero : Nat
  bits : Nat
  tbl : Nat
  J : Nat
  one : Nat

namespace JacWinCfg
variable (K : JacWinCfg)

def offset (J : Nat) : Nat := 16 * ((32^J-1)/31)
def E : Pt := ⟨K.T,K.T+32,K.T+64⟩
def z2 : Nat := K.T+96
def z3 : Nat := K.T+128

/-- Entry `m`, numbered from zero, coordinate `c < 5`. -/
def entry (m c : Nat) : Nat :=
  if c < 3 then K.tbl+96*m+32*c else K.tbl+1536+64*m+32*(c-3)

def tc : TCombCfg where
  M := K.M
  F := K.F
  ptr := 0
  S := K.S
  A := K.R
  E := K.E
  D := K.D
  neg := K.neg
  zero := K.zero
  bits := K.bits
  kbytes := 5*K.J
  tsym := ""
  w := 5
  J := K.J
  start := (0,0)
  one := K.one

/-- The two packed tables contain 96 and 64 bytes per entry. Only the
selection uses these synthetic word counts; field arithmetic uses `K.M`. -/
def scan (cache : Bool) : TCombCfg :=
  { K.tc with M := { K.M with n := if cache then 4 else 6 }
              E := ⟨K.T+(if cache then 96 else 0),0,0⟩ }

def tablePtr (tbl : Nat) : List Instr :=
  [.mov .edx (.reg .edi),.alu .add .edx (.imm (BitVec.ofNat 32 tbl))]

def selectPart (cache : Bool) : List Instr :=
  tablePtr (K.tbl+(if cache then 1536 else 0)) ++ (K.scan cache).selPass

def select : List Instr := K.selectPart false ++ K.selectPart true

/-- The address of a packed entry `esi - 1`, in `edx`. -/
def entryAddr (cache : Bool) : List Instr :=
  [.mov .eax (.reg .esi),.alu .sub .eax (.imm 1),
   .mov .ecx (.imm (if cache then 64 else 96)),.mul .ecx,
   .mov .edx (.reg .edi),
   .alu .add .edx (.imm (BitVec.ofNat 32 (K.tbl+(if cache then 1536 else 0)))),
   .alu .add .edx (.reg .eax)]

def storePart (cache : Bool) : List Instr :=
  K.entryAddr cache ++ Naf.copyPieces (if cache then 4 else 6)
    (fun i => sc (K.T+(if cache then 96 else 0)+16*i))
    (fun i => TCombCfg.tblAt (16*i))

def storeEntry : List Instr := K.storePart false ++ K.storePart true

def cacheOps : List FOp := [.mul K.z2 K.E.z K.E.z,.mul K.z3 K.z2 K.E.z]
def maddOps : List FOp := jacMixedHead K.S K.E K.P ++ jacMixedTail K.S K.E K.P K.E

/-- Cached-power Jacobian header: six products rather than nine. -/
def addHead : List FOp := CachedJac.head 4 K.S K.R K.E K.z2

def addOps : List FOp := K.addHead ++ jacTail K.S K.R K.E K.D

/-- Doubling in place, using the eight-product formula for a = -3. -/
def dbl (p : Pt) : Prog isa := fprog K.F (dblJMul K.S p p)

def buildStep : Prog isa :=
  .seq (.block ([.alu .add .esi (.imm 1)] ++ copy 8 K.S.t2 K.E.x ++ copy 8 K.S.t4 K.E.y)) <|
  .seq (fprog K.F (K.maddOps++K.cacheOps)) <|
  .block (K.storeEntry++[.alu .cmp .esi (.imm 16)])

def build : Prog isa :=
  .seq (.block (copyPt 4 K.E K.P ++ copy 8 K.z2 K.P.z ++ copy 8 K.z3 K.P.z ++
    [.mov .esi (.imm 1)] ++ K.storeEntry)) <|
  .seq (K.dbl K.E) <|
  .seq (fprog K.F K.cacheOps) <|
  .seq (.block ([.mov .esi (.imm 2)]++K.storeEntry)) <|
  .loop K.buildStep .ne

/-- The inner counter occupies high bits of the public window counter. -/
def dblStep : Prog isa :=
  .seq (K.dbl K.R) (.block [.alu .sub .esi (.imm 4096),.alu .cmp .esi (.imm 4096)])

def dbls : Prog isa :=
  .seq (.block [.alu .add .esi (.imm 20480)]) (.loop K.dblStep .ae)

def step : Prog isa :=
  .seq (.block [.alu .sub .esi (.imm 1)]) <|
  .seq K.dbls <|
  .seq (.block (K.tc.digit++K.select)) <|
  .seq K.tc.negY <|
  .seq (fprog K.F K.addOps) <|
  .block (nzMask 4 K.R.z ++ selPt 4 K.D K.E K.D ++
    K.tc.digit ++ eqMask 0 ++ selPt 4 K.R K.D K.R ++ [.alu .test .esi (.reg .esi)])

/-- Seed the accumulator from the highest digit, avoiding five initial doublings. -/
def first : Prog isa :=
  .seq (.block ([.mov .esi (.imm (BitVec.ofNat 32 (K.J-1)))]++K.tc.digit++K.select)) <|
  .seq K.tc.negY <| .block (copyPt 4 K.R K.E)

def finish : Prog isa := .seq (.block K.tc.outFix) (fprog K.F K.tc.outOps)
def window : Prog isa :=
  .seq K.build <| .seq K.first <| .seq (.loop K.step .ne) K.finish

end JacWinCfg
end VG.Impl.Weierstrass.X86
