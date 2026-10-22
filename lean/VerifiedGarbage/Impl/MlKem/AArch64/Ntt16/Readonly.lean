module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16

/-! Transform kernels with immutable roots, retaining the measured instructions. -/

@[expose] public section
namespace VG.Impl.MlKem.AArch64.Ntt16.Readonly
open VG.AArch64
open VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16

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
