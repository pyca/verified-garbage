module

public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyPublic
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyDerive
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyGenerate
import VerifiedGarbage.Proof.Dsa.X86_64.DeriveVerified
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallLayout
import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
public import VerifiedGarbage.Proof.Dsa.Contract

/-! # Key generation's calls, by their callees' leakage contracts -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

/-- The registers the domain check is called with. -/
def KeygenCheckRegs (s t : State) : Prop :=
  t.gpr .rdi = s.gpr .rcx ∧ t.gpr .rsi = s.gpr .r8 ∧ t.gpr .rdx = s.gpr .r9 ∧
    t.gpr .rcx = stackArg s 0 ∧ t.gpr .r8 = stackArg s 3 ∧ t.gpr .r9 = stackArg s 4

def KeygenCheckRelated (v : Backend) (a b : State) : Prop :=
  ∃ s t, ∃ hs : GenerateKeyABI v.stack s, ∃ ht : GenerateKeyABI v.stack t,
    KeygenState hs 0 a ∧ KeygenState ht 0 b ∧ KeygenCheckRegs s a ∧ KeygenCheckRegs t b ∧
    KeygenPublicAgree s t

theorem keygen_check_ct (v : Backend) : RelCT isa (KeygenCheckRelated v)
    (.call (keygenCheckName v) (Generate.checkParameters v.sq v.mul)) (fun _ _ => True) := by
  apply VG.X86_64.RelCT.callEx v.parametersVerified.1 v.parametersVerified.2.1
  intro a b ⟨s, t, hs, ht, ha, hb, ⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩, hp⟩
  obtain ⟨hca, hwa⟩ := keygen_check_covers hs ha.rd ha.wr
  obtain ⟨hcb, hwb⟩ := keygen_check_covers ht hb.rd hb.wr
  refine ⟨keygenCheckRd s, keygenCheckWr s, keygenCheckRd t, keygenCheckWr t,
    keygen_check_pre hs ha.sp a1 a2 a3 a4 a5 a6, keygen_check_pre ht hb.sp b1 b2 b3 b4 b5 b6, ?_,
    hca, hwa, hcb, hwb, ha.sp.trans (hp.base.trans hb.sp.symm)⟩
  sig_pub [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
  rw [show a.mem.writeW (a.gpr .rsp - 8) (a.unknowns 0) = a.callEntry.mem from rfl,
    show b.mem.writeW (b.gpr .rsp - 8) (b.unknowns 0) = b.callEntry.mem from rfl, a1, a2, b1, b2,
    keygen_callEntry_bytes hs ha.sp hs.stackParams (s.gpr .r8).isLt,
    keygen_callEntry_bytes ht hb.sp ht.stackParams (t.gpr .r8).isLt, keygen_bytes_params ha,
    keygen_bytes_params hb, hp.params, a3, a4, a5, a6, b3, b4, b5, b6, ha.sp, hb.sp, hp.base]
  exact ⟨rfl, rfl, hp.regs .rcx (by decide), hp.regs .r8 (by decide), hp.regs .r9 (by decide),
    hp.args 0 (by decide), hp.args 3 (by decide), hp.args 4 (by decide)⟩

/-- The registers and outgoing words the derivation is called with. -/
def KeygenDeriveRegs (s t : State) : Prop :=
  t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = s.gpr .rcx ∧ t.gpr .rcx = s.gpr .r8 ∧
    t.gpr .r8 = s.gpr .r9 ∧ t.gpr .r9 = off (randomBase s) Random.oNonce ∧
    ∀ i < 3, word t.mem (randomBase s) (8 * i) = keygenDeriveArg s i

/-- The derivation's status from the x in the frame. -/
def keygenDeriveStatus (s a : State) : Nat :=
  Spec.Dsa.signStatus (Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
    (Spec.Rsa.bytesAt a.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat))

def KeygenDeriveRelated (v : Backend) (a b : State) : Prop :=
  ∃ s t, ∃ hs : GenerateKeyABI v.stack s, ∃ ht : GenerateKeyABI v.stack t, ∃ ua ub : Nat,
    KeygenState hs ua a ∧ KeygenState ht ub b ∧ KeygenDeriveRegs s a ∧ KeygenDeriveRegs t b ∧
    KeygenPublicAgree s t ∧ keygenDeriveStatus s a = keygenDeriveStatus t b

theorem keygen_derive_ct (v : Backend) : RelCT isa (KeygenDeriveRelated v)
    (.call (keygenDeriveName v) (Generate.deriveKey v.sq v.mul)) (fun _ _ => True) := by
  apply VG.X86_64.RelCT.callEx v.deriveVerified.1 v.deriveVerified.2.1
  intro a b ⟨s, t, hs, ht, _, _, ha, hb, ⟨a1, a2, a3, a4, a5, a6, aw⟩, ⟨b1, b2, b3, b4, b5, b6, bw⟩, hp, hst⟩
  obtain ⟨hca, hwa⟩ := keygen_derive_covers hs ha.rd ha.wr
  obtain ⟨hcb, hwb⟩ := keygen_derive_covers ht hb.rd hb.wr
  refine ⟨keygenDeriveRd s, keygenDeriveWr s, keygenDeriveRd t, keygenDeriveWr t,
    keygen_derive_pre hs ha.sp aw a1 a2 a3 a4 a5 a6, keygen_derive_pre ht hb.sp bw b1 b2 b3 b4 b5 b6, ?_,
    hca, hwa, hcb, hwb, ha.sp.trans (hp.base.trans hb.sp.symm)⟩
  have hA (i : Nat) (hi : i < 3) :
      stackArg (a.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) i = keygenDeriveArg s i :=
    (random_call_stackArg ha.sp _ _ (by omega)).trans (aw i hi)
  have hB (i : Nat) (hi : i < 3) :
      stackArg (b.callEntry.withRegions (keygenDeriveRd t) (keygenDeriveWr t)) i = keygenDeriveArg t i :=
    (random_call_stackArg hb.sp _ _ (by omega)).trans (bw i hi)
  sig_pub [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three]
  simp only [hA 0 (by decide), hA 1 (by decide), hA 2 (by decide), hB 0 (by decide), hB 1 (by decide),
    hB 2 (by decide), keygenDeriveArg, List.getD_cons_succ, List.getD_cons_zero]
  rw [show a.mem.writeW (a.gpr .rsp - 8) (a.unknowns 0) = a.callEntry.mem from rfl,
    show b.mem.writeW (b.gpr .rsp - 8) (b.unknowns 0) = b.callEntry.mem from rfl, a3, a4, a5, a6, b3, b4, b5, b6,
    keygen_callEntry_bytes hs ha.sp hs.stackParams (s.gpr .r8).isLt,
    keygen_callEntry_bytes ht hb.sp ht.stackParams (t.gpr .r8).isLt,
    keygen_callEntry_nonce hs ha.sp, keygen_callEntry_nonce ht hb.sp,
    keygen_bytes_params ha, keygen_bytes_params hb, a1, a2, b1, b2, ha.sp, hb.sp]
  refine ⟨by rw [hp.base], ?_, hp.regs .rdi (by decide), hp.regs .rsi (by decide), hp.regs .rcx (by decide),
    hp.regs .r8 (by decide), hp.regs .r9 (by decide), by rw [hp.base], hp.args 0 (by decide), hp.args 3 (by decide),
    hp.args 4 (by decide)⟩
  have hst' := hst
  unfold keygenDeriveStatus at hst'
  change List.map _ (keygenInput s).params ++ [Spec.Dsa.signStatus (Spec.Dsa.deriveKeyBytes (keygenInput s).pLen
    (keygenInput s).qLen _ _)] = List.map _ (keygenInput t).params ++ [Spec.Dsa.signStatus
    (Spec.Dsa.deriveKeyBytes (keygenInput t).pLen (keygenInput t).qLen _ _)]
  rw [hst', hp.params]

end VG.Proof.Dsa.X86_64
