import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackContract
import VerifiedGarbage.Spec.MlDsa.HighPack
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Round (hbM)

/-- Explicit non-overlapping buffers containing the zero polynomial. -/
def packSat (g : Nat) : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000,1024⟩]
  wr := [⟨0x2000,32*packWidth g⟩]

/-- Fully verified fused packing helper: semantic correctness, ABI,
constant-time execution, and a satisfiable shared contract. -/
theorem pack_verified {g : Nat} (hg : IsG g) :
    Verified AArch64.target (Impl.MlDsa.AArch64.Optimized.HighPack.code g)
      (highPackContract g AArch64.abi) := by
  refine Verified.of_correct (pack_correct hg) (pack_ct hg) ?_
  refine { pre := ?_,post := ?_,pub := ?_,sat := ?_ }
  · rcases hg with rfl | rfl <;>
      (intro s h
       sig_pre [highPackContract,highPackSig,packK,packWidth,AArch64.abi,AArch64.argRegs] at h
       sig_split h
       sig_reduce [highPackContract,highPackSig,packK,packWidth,AArch64.abi,AArch64.argRegs]
       exact ⟨by assumption,by assumption,by assumption,h⟩)
  · rcases hg with rfl | rfl <;>
      sig_implies_post [highPackContract,highPackSig,packK,packWidth,highPacked,highCoefficients,hbM,AArch64.abi,AArch64.argRegs]
  · rcases hg with rfl | rfl <;>
      sig_implies_pub [highPackContract,highPackSig,packK,AArch64.abi,AArch64.argRegs]
  · refine ⟨packSat g,?_⟩
    rcases hg with rfl | rfl <;>
      sig_pre [highPackContract,highPackSig,AArch64.abi,AArch64.argRegs] <;> sig_and_intros
    all_goals first
      | rfl
      | exact Region.disjoint_of_sep (by decide)
      | exact fun i _ => by rw [VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero]; decide
      | decide

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
