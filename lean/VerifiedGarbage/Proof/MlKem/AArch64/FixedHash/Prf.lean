module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.PrfUsing
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHash
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64.Kem

/-- The PRF's hash, calling the permutation `c`. -/
def prfHash (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
 Impl.MlKem.AArch64.FixedHash.code c .x28 KEM.ST KEM.WK 136 31
 [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩]
theorem prfHash_valid (v : Proof.Sha3.AArch64.Permutation) : PrfHashValid (prfHash v.callee) := by
 intro s hs hi ho
 simpa only [prfHash,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,pbytes]
  using prf768_correct v hs (by decide) (by decide) hi ho (by simp)

/-- `PRF₂` and `SamplePolyCBD₂`, with the polynomial stored with 16 bits. -/
def prfW (c : Impl.Sha3.AArch64.Callee) : Nat→Nat→Prog isa :=
 fun N off => Impl.MlKem.AArch64.Optimized.prfCbdUsing (prfHash c) N off true

theorem prfW_valid (v : Proof.Sha3.AArch64.Permutation) {P : KemLay} {L : Layout} : PrfValidW P L (prfW v.callee) :=
 prf_using_validW (prfHash_valid v)
end VG.Proof.MlKem.AArch64.FixedHash
