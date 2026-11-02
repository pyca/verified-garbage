module

public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyPublic
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyGenerate
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyDerivePre
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveVerified
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallLayout
import VerifiedGarbage.Proof.Dsa.AArch64.ParametersVerified
public import VerifiedGarbage.Proof.Dsa.Contract

/-! # Key generation's calls, by their callees' leakage contracts -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

/-- The registers the domain check is called with. -/
def KeygenCheckRegs (s t : State) : Prop :=
  t.gpr .x0 = s.gpr .x3 ∧ t.gpr .x1 = s.gpr .x4 ∧ t.gpr .x2 = s.gpr .x5 ∧
    t.gpr .x3 = s.gpr .x6 ∧ t.gpr .x4 = stackArg s 1 ∧ t.gpr .x5 = stackArg s 2

def KeygenCheckRelated (v : Backend) (a b : State) : Prop :=
  ∃ s t, ∃ hs : GenerateKeyABI v.stack s, ∃ ht : GenerateKeyABI v.stack t,
    KeygenState hs 0 a ∧ KeygenState ht 0 b ∧ KeygenCheckRegs s a ∧ KeygenCheckRegs t b ∧
    KeygenPublicAgree s t

theorem keygen_check_ct (v : Backend) : RelCT isa (KeygenCheckRelated v)
    (.call (keygenCheckName v) (Generate.checkParameters v.mul)) (fun _ _ => True) := by
  apply VG.AArch64.RelCT.callEx v.parametersVerified.1 v.parametersVerified.2.1
  intro a b ⟨s, t, hs, ht, ha, hb, ⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩, hp⟩
  obtain ⟨hca, hwa⟩ := keygen_check_covers hs ha.rd ha.wr
  obtain ⟨hcb, hwb⟩ := keygen_check_covers ht hb.rd hb.wr
  refine ⟨keygenCheckRd s, keygenCheckWr s, keygenCheckRd t, keygenCheckWr t,
    keygen_check_pre hs ha.sp a1 a2 a3 a4 a5 a6, keygen_check_pre ht hb.sp b1 b2 b3 b4 b5 b6, ?_,
    hca, hwa, hcb, hwb⟩
  sig_pub [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
  rw [a1, a2, b1, b2, keygen_bytes_params ha, keygen_bytes_params hb, hp.params,
    a3, a4, a5, a6, b3, b4, b5, b6, ha.sp, hb.sp, hp.base]
  exact ⟨rfl, rfl, hp.regs .x3 (by decide), hp.regs .x4 (by decide), hp.regs .x5 (by decide),
    hp.regs .x6 (by decide), hp.args 1 (by decide), hp.args 2 (by decide)⟩

/-- The registers and outgoing words the derivation is called with. -/
def KeygenDeriveRegs (s t : State) : Prop :=
  t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x2 = s.gpr .x3 ∧ t.gpr .x3 = s.gpr .x4 ∧
    t.gpr .x4 = s.gpr .x5 ∧ t.gpr .x5 = off (randomBase s) Random.oNonce ∧
    t.gpr .x6 = s.gpr .x6 ∧ t.gpr .x7 = stackArg s 1 ∧
    word t.mem (randomBase s) 0 = stackArg s 2

/-- The derivation's status from the x in the frame. -/
def keygenDeriveStatus (s a : State) : Nat :=
  Spec.Dsa.signStatus (Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
    (Spec.Rsa.bytesAt a.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat))

def KeygenDeriveRelated (v : Backend) (a b : State) : Prop :=
  ∃ s t, ∃ hs : GenerateKeyABI v.stack s, ∃ ht : GenerateKeyABI v.stack t, ∃ ua ub : Nat,
    KeygenState hs ua a ∧ KeygenState ht ub b ∧ KeygenDeriveRegs s a ∧ KeygenDeriveRegs t b ∧
    KeygenPublicAgree s t ∧ keygenDeriveStatus s a = keygenDeriveStatus t b

theorem keygen_derive_ct (v : Backend) : RelCT isa (KeygenDeriveRelated v)
    (.call (keygenDeriveName v) (Generate.deriveKey v.mul)) (fun _ _ => True) := by
  apply VG.AArch64.RelCT.callEx v.deriveVerified.1 v.deriveVerified.2.1
  intro a b ⟨s, t, hs, ht, _, _, ha, hb, ⟨a1, a2, a3, a4, a5, a6, a7, a8, aw⟩, ⟨b1, b2, b3, b4, b5, b6, b7, b8, bw⟩, hp, hst⟩
  obtain ⟨hca, hwa⟩ := keygen_derive_covers hs ha.rd ha.wr
  obtain ⟨hcb, hwb⟩ := keygen_derive_covers ht hb.rd hb.wr
  refine ⟨keygenDeriveRd s, keygenDeriveWr s, keygenDeriveRd t, keygenDeriveWr t,
    keygen_derive_pre hs ha.sp aw a1 a2 a3 a4 a5 a6 a7 a8, keygen_derive_pre ht hb.sp bw b1 b2 b3 b4 b5 b6 b7 b8, ?_,
    hca, hwa, hcb, hwb⟩
  have hA : stackArg (a.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) 0 = stackArg s 2 :=
    (random_call_stackArg ha.sp _ _ 0).trans aw
  have hB : stackArg (b.callEntry.withRegions (keygenDeriveRd t) (keygenDeriveWr t)) 0 = stackArg t 2 :=
    (random_call_stackArg hb.sp _ _ 0).trans bw
  sig_pub [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  simp only [hA, hB, List.getD_cons_succ, List.getD_cons_zero]
  rw [a3, a4, a5, a6, a7, a8, b3, b4, b5, b6, b7, b8,
    keygen_bytes_params ha, keygen_bytes_params hb, a1, a2, b1, b2, ha.sp, hb.sp]
  refine ⟨by rw [hp.base], ?_, hp.regs .x0 (by decide), hp.regs .x1 (by decide), hp.regs .x3 (by decide),
    hp.regs .x4 (by decide), hp.regs .x5 (by decide), by rw [hp.base], hp.regs .x6 (by decide), hp.args 1 (by decide),
    hp.args 2 (by decide)⟩
  have hst' := hst
  unfold keygenDeriveStatus at hst'
  change List.map _ (keygenInput s).params ++ [Spec.Dsa.signStatus (Spec.Dsa.deriveKeyBytes (keygenInput s).pLen
    (keygenInput s).qLen _ _)] = List.map _ (keygenInput t).params ++ [Spec.Dsa.signStatus
    (Spec.Dsa.deriveKeyBytes (keygenInput t).pLen (keygenInput t).qLen _ _)]
  rw [hst', hp.params]

end VG.Proof.Dsa.AArch64
