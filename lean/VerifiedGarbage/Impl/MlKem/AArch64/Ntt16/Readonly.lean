module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16

/-! Transform kernels with immutable roots, retaining the measured instructions. -/

@[expose] public section
namespace VG.Impl.MlKem.AArch64.Ntt16.Readonly
open VG.AArch64
open VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16

def fwd : Prog isa :=
 .seq (.block (consts ++ [mov .x2 .x0,mov .x3 .x1,.movz .x .x5 4 0]))
 (.seq (.loop (.block pass1Body) (.nonzero .x .x5))
 (.seq (.block [mov .x2 .x1,.adrSym .x6 "VG_MLKEM_NTT16_ZETAS",mov .x4 .x0,.movz .x .x5 8 0])
 (.loop (.block pass2Body) (.nonzero .x .x5))))
/-- `fwd` of a polynomial stored with 16-bit coefficients (`pass1BodyW`, `pass2BodyW`). -/
def fwdW : Prog isa :=
 .seq (.block (consts ++ [mov .x2 .x0,mov .x3 .x1,.movz .x .x5 4 0]))
 (.seq (.loop (.block pass1BodyW) (.nonzero .x .x5))
 (.seq (.block [mov .x2 .x1,.adrSym .x6 "VG_MLKEM_NTT16_ZETAS",mov .x4 .x0,.movz .x .x5 8 0])
 (.loop (.block pass2BodyW) (.nonzero .x .x5))))
def inv : Prog isa :=
 .seq (.block (qConsts ++ [mov .x2 .x0,mov .x3 .x1,.adrSym .x6 "VG_MLKEM_INTT16_ZETAS",.movz .x .x5 8 0]))
 (.seq (.loop (.block invPass1Body) (.nonzero .x .x5))
 (.seq (.block (invConsts ++ [mov .x2 .x1,mov .x3 .x0,.movz .x .x5 4 0]))
 (.loop (.block invPass2Body) (.nonzero .x .x5))))
def mul : Prog isa :=
 .seq (.block (vconsts ++ [.adrSym .x3 "VG_MLKEM_GAMMA",.movz .x .x11 32 0]))
 (.loop (.block vmulBody) (.nonzero .x .x11))
def words (bits : Nat) (xs : List Nat) : List (BitVec 64) :=
 (List.range (xs.length/(64/bits))).map fun i => BitVec.ofNat 64
  ((List.range (64/bits)).foldl (fun n j => n + xs.getD (i*(64/bits)+j) 0 * 2^(bits*j)) 0)
def tables : List (String × List (BitVec 64)) :=
 [("VG_MLKEM_NTT16_ZETAS",words 16 tableHalves),("VG_MLKEM_INTT16_ZETAS",words 16 invTableHalves),
  ("VG_MLKEM_GAMMA",words 32 gammaTable)]

end VG.Impl.MlKem.AArch64.Ntt16.Readonly
