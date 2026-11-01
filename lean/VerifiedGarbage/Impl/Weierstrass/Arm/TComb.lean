module

public import VerifiedGarbage.Impl.Weierstrass.Arm.LadderP
import VerifiedGarbage.Impl.Weierstrass.TCombWords

/-! Fixed-base signed comb using the same tables and scalar decomposition as P-256.
The table address depends only on the public row counter. Every row entry is scanned.
-/

@[expose] public section
namespace VG.Impl.Weierstrass.Arm
open VG VG.Arm VG.Impl.Weierstrass VG.Impl.Mont.Arm
open Point

structure TCombCfg where
 L : LadderCfg
 F : Impl.Weierstrass.Mont.Modulus
 w : Nat
 J : Nat
 tsym : String
 start : Nat × Nat
 one : Nat
 zero : Nat
 neg : Nat
 /-- Whether the point functions called are the `_umaal` variants. -/
 u : Bool := false

namespace TCombCfg
variable (K : TCombCfg)
def H : Nat := 2^(K.w-1)
def P : Pt := ptAt K.L.M.n (Impl.Weierstrass.Point.pAt K.L.M.n)
def Q : Pt := ptAt K.L.M.n (Impl.Weierstrass.Point.qAt K.L.M.n)
def O : Pt := ptAt K.L.M.n (Impl.Weierstrass.Point.oAt K.L.M.n)
/-- The same Horner decoding used by the other comb backends. -/
def hornerAt : Nat → Nat → List Instr
 | _, 0 => [.mov .r9 (.imm 0)]
 | d, k+1 => hornerAt (d+1) k ++ [.dp .add .r9 .r9 (.reg .r9),
      .ldrb .r5 .r4 (K.L.bits%4096+d), .dp .add .r9 .r9 (.reg .r5)]

def horner (k : Nat) : List Instr := K.hornerAt 0 k

def topBits : Nat := K.L.nbits - K.w*(K.J-1)
def lastTest : List Instr := [.cmp .r11 (.imm (BitVec.ofNat 32 (K.J-1)))]
def magnitude : List Instr :=
 [.dp .sub .r9 .r9 (.imm (BitVec.ofNat 32 K.H)),
  .mov .r4 (.shifted .r9 .lsr 31), .mov .r5 (.imm 0),
  .dp .sub .r4 .r5 (.reg .r4), .dp .eor .r9 .r9 (.reg .r4), .dp .sub .r9 .r9 (.reg .r4)]

/-- Public window address, shared by digit and sign decoding. -/
def windowIndex : List Instr :=
 [.mov .r4 (.imm (BitVec.ofNat 32 K.w)), .mul .r4 .r4 .r11,
  .dp .add .r4 wb (.reg .r4)] ++ far .r4 K.L.bits

def digit : Prog isa :=
 .seq (.block K.windowIndex) <|
 .seq (.block K.lastTest) <|
 .seq (.ite .eq (.block (K.horner K.topBits)) (.block (K.horner K.w))) (.block K.magnitude)

def eqMask (index : Op2) : List Instr :=
 [.dp .eor .r10 .r9 index, .dp .sub .r10 .r10 (.imm 1),
  .mov .r10 (.shifted .r10 .lsr 31), .mov .r5 (.imm 0), .dp .sub .r10 .r5 (.reg .r10)]

def selectWord (i : Nat) : List Instr :=
 [.ldr .r4 wb (K.Q.x+4*i), .ldr .r5 .r8 (4*i),
  .dp .eor .r5 .r5 (.reg .r4), .dp .and .r5 .r5 (.reg .r10),
  .dp .eor .r4 .r4 (.reg .r5), .str .r4 wb (K.Q.x+4*i)]
def selectBody : List Instr := eqMask (.reg .r7) ++
 (List.range (4*K.L.M.n)).flatMap (K.selectWord) ++
 [.dp .add .r8 .r8 (.imm (BitVec.ofNat 32 (16*K.L.M.n))),
  .dp .add .r7 .r7 (.imm 1), .cmp .r7 (.imm (BitVec.ofNat 32 (K.H+1)))]

def selectSetup : List Instr :=
 [.adrSym .r8 K.tsym, .mov .r4 (.imm (BitVec.ofNat 32 (16*K.L.M.n*K.H))),
   .mul .r4 .r4 .r11, .dp .add .r8 .r8 (.reg .r4)] ++
 setConst K.L.M.n K.Q.x 0 ++ setConst K.L.M.n K.Q.y 0 ++ [.mov .r7 (.imm 1)]

def selectTail : List Instr :=
 setConst K.L.M.n K.Q.z K.one ++ eqMask (.imm 0) ++
 sel (2*K.L.M.n) K.Q.y K.Q.y K.Q.z ++ sel (2*K.L.M.n) K.Q.z K.Q.z K.zero

def select : Prog isa :=
 .seq (.block K.selectSetup) (.seq (.loop (.block K.selectBody) .ne) (.block K.selectTail))

def signRead : List Instr := K.windowIndex ++
 [.ldrb .r4 .r4 (K.L.bits%4096+K.w-1), .dp .sub .r10 .r4 (.imm 1)]

def signMask : Prog isa :=
 if K.topBits<K.w then
  .seq (.block K.lastTest) (.ite .eq (.block [.movw .r10 0xffff,.movt .r10 0xffff]) (.block K.signRead))
 else .block K.signRead

/-- A selected signed table entry; arithmetic is shared with the ladder. -/
def entry : Prog isa :=
 .seq K.digit <| .seq K.select <|
 .seq (Mont.subCall K.F K.neg K.zero K.Q.y) <|
 .seq K.signMask (.block (sel (2*K.L.M.n) K.Q.y K.Q.y K.neg))

/-- Add the selected entry through the existing point function. -/
def add : Prog isa :=
 .seq (.block (copyPt K.L.M.n K.P K.L.R)) <|
 .seq (ptCall K.F false false K.u) (.block (copyPt K.L.M.n K.L.R K.O))

def step : Prog isa :=
 .seq (.block [decCounter]) <| .seq K.entry <| .seq K.add (.block [testCounter])

def comb : Prog isa :=
 .seq (.block (ladderSetup K.L ++
   setConst K.L.M.n K.L.R.x K.start.1 ++ setConst K.L.M.n K.L.R.y K.start.2 ++
   setConst K.L.M.n K.L.R.z K.one ++ [.mov .r11 (.imm (BitVec.ofNat 32 K.J))]))
 (.loop K.step .ne)

end TCombCfg
end VG.Impl.Weierstrass.Arm
