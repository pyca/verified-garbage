import VerifiedGarbage.Impl.Weierstrass.X86.InvMemory

/-! # Batched inversion for 256-bit moduli on 32-bit x86

Twenty batches of thirty divsteps update nine-word signed `f,g` and
eight-word reduced coefficients `a,b`. Each coefficient reduction divides
by `2^32`, so the final Montgomery factor includes `2^(2*20)`.
-/
namespace VG.Impl.Weierstrass.X86
open VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv

def setWord (dst : Nat) (x : BitVec 32) : List Instr :=
  [.mov .eax (.imm x), .store (sc dst) .eax]

def copyPad (dst src : Nat) : List Instr := copy 8 dst src ++ zeros (dst + 32) 1

def one8 (dst : Nat) : List Instr := zeros dst 8 ++ setWord dst 1

structure InvCfg where
  M : Mod
  wk : Nat
  out : Nat
  base : Nat
  tbl : Nat
  C : Nat
  Cn : Nat

namespace InvCfg
variable (P : InvCfg)

def sF : Nat := P.tbl
def sG : Nat := P.tbl + 36
def sA : Nat := P.tbl + 72
def sB : Nat := P.tbl + 104
def sNF : Nat := P.tbl + 136
def sNG : Nat := P.tbl + 172
def sT : Nat := P.tbl + 208
def sU : Nat := P.tbl + 252
def sW : Nat := P.tbl + 288
def sCount : Nat := P.tbl + 316

def init : List Instr :=
  copyPad P.sF P.M.mo ++ copyPad P.sG P.base ++ zeros P.sA 8 ++ one8 P.sB ++
    setWord P.sW 1 ++ setWord P.sCount 20

def batchStart : List Instr :=
  copy 1 (P.sW + 4) P.sF ++ copy 1 (P.sW + 8) P.sG ++
    setConst 2 (P.sW + 12) (1 + 2 ^ 96)

def fgUpdate : List Instr :=
  linear (P.sW + 12) (P.sW + 16) P.sT P.sF P.sG P.sU 9 7 ++ shr30 P.sNF P.sT 9 ++
    linear (P.sW + 20) (P.sW + 24) P.sT P.sF P.sG P.sU 9 7 ++ shr30 P.sNG P.sT 9 ++
    copy 9 P.sF P.sNF ++ copy 9 P.sG P.sNG

def abUpdate : List Instr :=
  linear (P.sW + 12) (P.sW + 16) P.sT P.sA P.sB P.sU 8 7 ++ reduce P.M P.sT P.sU P.sNF ++
    linear (P.sW + 20) (P.sW + 24) P.sT P.sA P.sB P.sU 8 7 ++ reduce P.M P.sT P.sU P.sB ++
    copy 8 P.sA P.sNF

def batchEnd : List Instr :=
  [.mov .esi (.mem (sc P.sCount)), decCounter, .store (sc P.sCount) .esi, testCounter]

def batch : Prog isa :=
  .seq (.seq (.block P.batchStart) (wordSteps P.sW 30)) (.block (P.fgUpdate ++ P.abUpdate ++ P.batchEnd))

def finish : Prog isa :=
  .seq (.block (setConst 4 P.sNF P.C ++ setConst 4 P.sNG P.Cn ++ maskOf P.sF ++ sel 8 P.sNF P.sNF P.sNG))
    (Mont.X86.mul P.M P.wk P.out P.sA P.sNF)

def inv : Prog isa := .seq (.block P.init) (.seq (.loop P.batch .ne) P.finish)

def ofMod (M : Mod) (wk out base tbl modulus : Nat) : InvCfg :=
  let C := 2 ^ 40 * (2 ^ 256) ^ 3 % modulus
  { M, wk, out, base, tbl, C, Cn := modulus - C }

end InvCfg
end VG.Impl.Weierstrass.X86
