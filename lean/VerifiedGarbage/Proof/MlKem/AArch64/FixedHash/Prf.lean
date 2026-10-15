module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.PrfUsing
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64.Kem

def prfHash : Prog isa :=
 Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 31
 [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩]
def prf : Nat→Nat→Prog isa := Impl.MlKem.AArch64.Optimized.prfCbdUsing prfHash

theorem prfHash_valid : PrfHashValid prfHash := by
 intro s hs hi ho
 simpa only [prfHash,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,pbytes]
  using prf768_correct hs (by decide) (by decide) hi ho (by simp)

theorem prf_valid {P : KemLay} {L : Layout} : PrfValid P L prf :=
 prf_using_valid prfHash_valid
end VG.Proof.MlKem.AArch64.FixedHash
