import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackTiming
import VerifiedGarbage.Spec.MlDsa.UseHintPack
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open HighPack (packWidth)

def packSat (g : Nat) : State where
  gpr r := match r with | .x0=>0x1000 | .x1=>0x2000 | .x2=>0x3000 | .x3=>BitVec.ofNat 64 g | _=>0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000,1024⟩,⟨0x3000,1024⟩]
  wr := [⟨0x1000,32*packWidth g⟩]

/-- Fused UseHint and encoding against the architecture-independent shared specification. -/
theorem pack_verified {g : Nat} (hg : IsG g) :
    Verified AArch64.target Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
      (useHintPackContract g AArch64.abi) := by
  refine Verified.of_correct (pack_correct hg) pack_ct ?_
  refine {pre:=?_,post:=?_,pub:=?_,sat:=?_}
  · rcases hg with rfl|rfl <;>
      (intro s h
       sig_pre [useHintPackContract,useHintPackSig,packK,packWidth,AArch64.abi,AArch64.argRegs] at h
       sig_split h
       sig_reduce [packK,packWidth,arg32]
       exact ⟨by assumption,by assumption,by apply Region.Disjoint.symm; assumption,by apply Region.Disjoint.symm; assumption,by assumption,by assumption⟩)
  · intro s t hp hpost
    have hr : Reduced s.mem (s.gpr .x2) := by
      rcases hg with rfl|rfl <;>
        (sig_pre [useHintPackContract,useHintPackSig,AArch64.abi,AArch64.argRegs] at hp
         sig_split hp
         exact hp)
    have hs := packed_spec hg (h:=s.gpr .x1) hr
    rcases hg with rfl|rfl <;>
      (sig_post [useHintPackContract,useHintPackSig,packK,packWidth,AArch64.abi,AArch64.argRegs]
       exact hpost.trans hs)
  · rcases hg with rfl|rfl <;>
      sig_implies_pub [useHintPackContract,useHintPackSig,packK,AArch64.abi,AArch64.argRegs]
  · refine ⟨packSat g,?_⟩
    rcases hg with rfl|rfl <;>
      sig_pre [useHintPackContract,useHintPackSig,AArch64.abi,AArch64.argRegs] <;> sig_and_intros
    all_goals first
      | rfl
      | exact Region.disjoint_of_sep (by decide)
      | exact fun i _=>by rw [VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero];decide
      | decide

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
