module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Instances
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ABI
import VerifiedGarbage.Proof.Dsa.X86.Generation.Correct
import VerifiedGarbage.Proof.Dsa.X86.Generation.TopCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.Satisfiable
import VerifiedGarbage.Proof.Dsa.X86.Generation.NoSp

/-! # DSA parameter generation on i686 is verified -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Dsa.X86.Generation

theorem body_noSp {g1 g2 g3 : Geo} (n1 : NoSp g1.generate) (n2 : NoSp g2.generate) (n3 : NoSp g3.generate) :
    NoSp (.seq (.seq (.block entry) (dispatch g1 g2 g3)) (.block VG.Impl.Mont.X86.Compact.restoreRegs)) := by
  apply NoSp.of_all
  simp only [dispatch, Code.allInstrs, checked n1, checked n2, checked n3]
  rfl

theorem generate1_noSp (v1 : Proof.Sha1.X86.Variants.Backend) (v : RoundImpl) : NoSp (geo1 v1 v).generate :=
  Geo.generate_noSp v1.cmpSp sha1_outNoSp (geo1Ok v1 v).qNoSp (geo1Ok v1 v).pNoSp (geo1Ok v1 v).cNoSp

theorem generate256_noSp (pLen : Nat) (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) :
    NoSp (geo256 pLen v256 v).generate :=
  Geo.generate_noSp v256.cmpSp sha256_outNoSp (ProbablePrime.code_noSp compact_noSp v.noSp _ _ _)
    (ProbablePrime.code_noSp compact_noSp v.noSp _ _ _) check_noSp

theorem verified (v1 : Proof.Sha1.X86.Variants.Backend) (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) :
    Verified target (code (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v)) genContract :=
  ⟨correct (geo1Ok v1 v) (geo2Ok v256 v) (geo3Ok v256 v) rfl rfl rfl
      (body_noSp (generate1_noSp v1 v) (generate256_noSp 256 v256 v) (generate256_noSp 384 v256 v)),
    constantTime (geo1Ok v1 v) (geo2Ok v256 v) (geo3Ok v256 v) rfl rfl rfl, satisfiable⟩

theorem writesSp_false {i : Instr} (h : VG.X86.Taint.clobbers i .esp = false) : isa.writesSp i = false := by
  cases i <;> simp_all [VG.X86.Taint.clobbers, VG.X86.Taint.dst, Instr.dst]

theorem code_all (v1 : Proof.Sha1.X86.Variants.Backend) (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) :
    (code (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v)).all (fun i => !isa.writesSp i) = true := by
  have hb := body_noSp (generate1_noSp v1 v) (generate256_noSp 256 v256 v) (generate256_noSp 384 v256 v)
  refine Code.all_of_allInstrs ?_
  simp only [code, Code.allInstrs]
  have inner : Code.allInstrs (fun i => !isa.writesSp i)
      (.seq (.seq (.block entry) (dispatch (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v)))
        (.block VG.Impl.Mont.X86.Compact.restoreRegs)) = true := by
    rw [Code.allInstrs_eq, List.all_eq_true]
    intro i hi
    rw [writesSp_false (hb i hi)]
    rfl
  simp only [Code.allInstrs] at inner
  simp only [inner]
  rfl

end VG.Proof.Dsa.X86.Generation
