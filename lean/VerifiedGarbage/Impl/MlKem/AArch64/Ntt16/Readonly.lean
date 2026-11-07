module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16

/-! Transform kernels with immutable roots, retaining the measured instructions. -/

@[expose] public section
namespace VG.Impl.MlKem.AArch64.Ntt16.Readonly
open VG.AArch64
open VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16

def words (bits : Nat) (xs : List Nat) : List (BitVec 64) :=
 (List.range (xs.length/(64/bits))).map fun i => BitVec.ofNat 64
  ((List.range (64/bits)).foldl (fun n j => n + xs.getD (i*(64/bits)+j) 0 * 2^(bits*j)) 0)
end VG.Impl.MlKem.AArch64.Ntt16.Readonly
