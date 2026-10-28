module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFields
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePort
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWriteOutputs
import VerifiedGarbage.Proof.RsaKeyGen.TruncatedOctets
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The masked native export returns the specified key or all zeros -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def WrittenCore (g : OutputGeometry) (e p q : Nat) (t : State) : Prop :=
  match Spec.RsaKeyGen.keyFromPrimes (32 * g.n) e p q with
  | .inl (.ok key) => (t.gpr .eax).toNat = 1 ∧
      ∀ i, i < 7 → Spec.Rsa.bytesAt t.mem (g.region i).base (g.region i).len =
        Spec.Rsa.i2osp (keyField key i) (g.length i)
  | .inr () => (t.gpr .eax).toNat = 2 ∧
      ∀ i, i < 7 → Spec.Rsa.bytesAt t.mem (g.region i).base (g.region i).len = List.replicate (g.length i) 0
  | .inl (.error _) => (t.gpr .eax).toNat = 0 ∧
      ∀ i, i < 7 → Spec.Rsa.bytesAt t.mem (g.region i).base (g.region i).len = List.replicate (g.length i) 0

/-- Any code that writes the masked outputs and returns the status writes the specified key. -/
theorem writeCore_of {g : OutputGeometry} {c : Prog isa} {s : State} {e p q : Nat} {R : State → Prop}
    (run : ∀ accept, slot s.mem g.base kOk = (if accept then 1 else 0) → WP isa c s fun t =>
      R t ∧ (t.gpr .eax).toNat = slot s.mem g.base kStatus ∧
      (∀ i, i < 7 → Spec.Rsa.bytesAt t.mem (g.region i).base (g.region i).len = portResult g s.mem accept i) ∧
      Frame g.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t)
    (result : CoreOutcome g.base g.n e p q s.mem) :
    WP isa c s fun t =>
      R t ∧ WrittenCore g e p q t ∧ Frame g.writes s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold CoreOutcome at result
  cases code : Spec.RsaKeyGen.keyFromPrimes (32 * g.n) e p q with
  | inr u =>
    cases u
    rw [code] at result
    obtain ⟨status, mask⟩ := result
    refine WP.mono (run false mask) fun t ⟨ht, ret, values, F, K⟩ => ?_
    refine ⟨ht, ?_, F, K⟩
    unfold WrittenCore
    rw [code]
    refine ⟨ret.trans status, ?_⟩
    intro i hi
    simpa only [portResult, Bool.false_eq_true, ite_false, Nat.zero_mod, VG.Proof.Bignum.i2osp_zero'] using values i hi
  | inl value =>
    cases value with
    | error failure =>
      rw [code] at result
      obtain ⟨status, mask⟩ := result
      refine WP.mono (run false mask) fun t ⟨ht, ret, values, F, K⟩ => ?_
      refine ⟨ht, ?_, F, K⟩
      unfold WrittenCore
      rw [code]
      refine ⟨ret.trans status, ?_⟩
      intro i hi
      simpa only [portResult, Bool.false_eq_true, ite_false, Nat.zero_mod, VG.Proof.Bignum.i2osp_zero'] using values i hi
    | ok key =>
      rw [code] at result
      obtain ⟨status, mask, assembled⟩ := result
      refine WP.mono (run true mask) fun t ⟨ht, ret, values, F, K⟩ => ?_
      refine ⟨ht, ?_, F, K⟩
      unfold WrittenCore
      rw [code]
      refine ⟨ret.trans status, ?_⟩
      intro i hi
      have value := values i hi
      change Spec.Rsa.bytesAt t.mem (g.region i).base (g.region i).len =
        Spec.Rsa.i2osp (num s.mem g.base g.n (outputIndex i) % 2 ^ (8 * g.length i)) (g.length i) at value
      rw [VG.Proof.RsaKeyGen.i2osp_mod] at value
      rw [assembled_field _ _ _ hi, assembled] at value
      exact value

theorem writeCore_ok {g : OutputGeometry} {s : State} {e p q : Nat} (h : OutputInput g s)
    (result : CoreOutcome g.base g.n e p q s.mem) :
    WP isa (writeOutputs g.n) s fun t =>
      Ws t g.base g.size g.n 32 ∧ WrittenCore g e p q t ∧ Frame g.writes s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
  writeCore_of (fun accept mask => writeOutputs_ok h accept mask) result

end VG.Proof.RsaKeyGen.X86.Key
