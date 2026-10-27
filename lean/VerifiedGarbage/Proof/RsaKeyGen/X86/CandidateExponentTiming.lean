module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentInitial
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentFilterTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentImportTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.SaveTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Candidate saving, public exponent import, and filtering have one composed timing proof -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateExponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.PublicContext

def InitialPair (workspace p e : BitVec 32) (size w c d len exponent : Nat) (s t : State) : Prop :=
  Initial workspace p e size w c len exponent s ∧ Initial workspace p e size w d len exponent t

theorem save_pair {workspace p e : BitVec 32} {size w c d len exponent : Nat} :
    RelCT isa (InitialPair workspace p e size w c d len exponent) VG.Impl.RsaKeyGen.X86.ExponentRt.save
      (ExponentImport.InputPair (workspace.setWidth 64) size) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := ExponentRt.save_trace _ _ _ _ _ _ ⟨H.1.spaceRt, H.2.spaceRt⟩ E G
  obtain ⟨Su, Ou, Ku⟩ := wp_result H.1.save_ok E
  obtain ⟨Sz, Oz, Kz⟩ := wp_result H.2.save_ok G
  have savedLo := H.1.savedLo
  refine ⟨trace, Su, Sz, agree, ?_, ?_⟩
  · rw [BitVec.eq_of_toNat_eq (Ou.w32 (d := 12) (by omega) (by decide)),
      BitVec.eq_of_toNat_eq (Oz.w32 (d := 12) (by omega) (by decide)), H.1.pointer, H.2.pointer]
  · apply BitVec.eq_of_toNat_eq
    change w32 u.mem (workspace.setWidth 64) 16 = w32 z.mem (workspace.setWidth 64) 16
    rw [Ou.w32 (d := 16) (by omega) (by decide), Oz.w32 (d := 16) (by omega) (by decide), H.1.length, H.2.length]

theorem prepare_trace {workspace p e : BitVec 32} {size w c d len exponent : Nat} :
    RelCT isa (InitialPair workspace p e size w c d len exponent)
      (.seq VG.Impl.RsaKeyGen.X86.ExponentRt.save VG.Impl.RsaKeyGen.X86.ExponentImport.code)
      (ExponentFilter.TimingPair workspace p size w c d exponent) := by
  intro s t tr ur u z H E G
  have raw : RelCT isa (InitialPair workspace p e size w c d len exponent)
      (.seq VG.Impl.RsaKeyGen.X86.ExponentRt.save VG.Impl.RsaKeyGen.X86.ExponentImport.code)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
    RelCT.seq save_pair (ExponentImport.code_trace (size := size) (by have := H.1.header; omega))
  exact ⟨(raw _ _ _ _ _ _ H E G).1, wp_result H.1.prepare_ok E, wp_result H.2.prepare_ok G⟩

theorem code_trace {workspace p e : BitVec 32} {size w c d len exponent : Nat} :
    RelCT isa (InitialPair workspace p e size w c d len exponent)
      VG.Impl.RsaKeyGen.X86.ExponentRt.code (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.ExponentRt.code
  exact RelCT.assoc (RelCT.seq prepare_trace ExponentFilter.code_trace)

end VG.Proof.RsaKeyGen.X86.CandidateExponent
