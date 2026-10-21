module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext

/-! # Native candidate arrays share the prepared round's public geometry -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.Proof.MillerRabin.X86 VG.Impl.Bignum.X86.PublicContext

theorem Environment.Valid.slotFit {E : Environment} (v : E.Valid) {j : Nat} (index : j < 28) :
    slot E.width j + 8 * E.width ≤ E.size := by
  have fit := v.geometry.arrayFit index
  rw [← Prepared.slot_eq] at fit
  change slot E.width j + 4 * (2 * E.width) ≤ E.size at fit
  omega

theorem Environment.slotHeader (E : Environment) (j : Nat) : 256 ≤ slot E.width j := by
  unfold slot VG.Impl.Bignum.hdrBytes
  omega

theorem Environment.slotBefore (E : Environment) {i j : Nat} (index : i < j) :
    slot E.width i + 8 * E.width ≤ slot E.width j := by
  have fit := E.geometry.arrayBefore index
  rw [← Prepared.slot_eq, ← Prepared.slot_eq] at fit
  change slot E.width i + 4 * (2 * E.width) ≤ slot E.width j at fit
  omega

end VG.Proof.RsaKeyGen.X86.Candidate
