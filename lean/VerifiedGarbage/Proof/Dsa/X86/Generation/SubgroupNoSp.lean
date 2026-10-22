module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Subgroup
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash

/-! Reuse the streaming hash stack-safety proofs in the subgroup wrapper. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem noSp_all {code : Prog isa} (h : NoSp code) :
    code.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  simpa using h i hi

theorem subgroup_body_noSp {H : Hash} (ok : HashOK H) (seedLen : Nat) :
    NoSp (.seq (.block (subgroupArguments seedLen))
      (qCandidate H 512 (VG.Impl.Dsa.Generation.Layout.q - subgroupHashScratch))) := by
  apply NoSp.of_all
  have init := noSp_all ok.initSp
  have update := noSp_all ok.updSp
  have finish := noSp_all ok.finSp
  simp only [qCandidate, seedHash, hashAbsorb, hashFinish, Hash.callInit, qArguments, qShape,
    subgroupArguments, Code.allInstrs,
    init, update, finish]
  rfl

end VG.Proof.Dsa.X86.Generation
