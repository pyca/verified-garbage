module

public import VerifiedGarbage.Proof.Camellia.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
public import VerifiedGarbage.Impl.Camellia.RISCV64.FbFinal
public import VerifiedGarbage.Spec.Camellia.CfbFinal
public import VerifiedGarbage.Spec.Camellia.OfbFinal
import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalLit
meta import VerifiedGarbage.Proof.Camellia.RISCV64.ModesVerified
meta import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
meta import VerifiedGarbage.Impl.Camellia.RISCV64.FbFinal
meta import VerifiedGarbage.Spec.Camellia.CfbFinal
meta import VerifiedGarbage.Spec.Camellia.OfbFinal
meta import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalLit

/-!
# Camellia-CFB128 and Camellia-OFB of a message's last piece on RISC-V meet their contracts

`modeFn` (`ModesVerified.lean`) of the modes' CFB and OFB over a message's
last piece (`Proof.Modes.RISCV64.cfbEncFinal_wp`, `cfbDecFinal_wp`,
`ofbFinal_wp`) over Camellia's encryption core (`Mode.dirCoreSpec`) meet the
contracts on the subkeys, and so the specification's
(`Proof.Camellia.cfbEncryptFinal_of_sk`, …, `Proof.Camellia.ofbFinal_of_sk`),
with `stack := 3264`, the whole-block functions' frame, whose precondition,
with the data `len` bytes, is `seq`'s for the data a byte at a time
(`byteMode`). Constant time as the whole-block functions.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64.Modes

open VG VG.RISCV64 VG.Impl.Camellia.RISCV64 VG.Impl.Modes
open VG.Proof.Modes.RISCV64 (SeqPre byteMode)
open VG.Proof.Camellia.RISCV64.Mode (dirCoreSpec KeyArgs layout)
open VG.Proof.Camellia.RISCV64 (modePub modes_ofRegs)
open VG.Proof.Camellia (schedWords)

/-- The final functions' postconditions. -/
def encFinalPost (s s' : State) : Prop :=
  Spec.Cfb.EncryptFinal (ciph s) 16 s.mem s'.mem (s.gpr .a2) (s.gpr .a3) (s.gpr .a4).toNat
def decFinalPost (s s' : State) : Prop :=
  Spec.Cfb.DecryptFinal (ciph s) 16 s.mem s'.mem (s.gpr .a2) (s.gpr .a3) (s.gpr .a4).toNat
def ofbFinalPost (s s' : State) : Prop :=
  Spec.Ofb.CryptFinal (ciph s) 16 s.mem s'.mem (s.gpr .a2) (s.gpr .a3) (s.gpr .a4).toNat

/-- A final function on RISC-V, with its frame below the stack pointer, the
data `len` bytes, and the postcondition `post`. -/
def finalContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 272⟩
    let iv : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes, frameBytes⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a0).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data ∧ ((s.gpr .a1).toNat = 18 ∨ (s.gpr .a1).toNat = 24)
  post s s' := ((s.gpr .a1).toNat = 18 ∨ (s.gpr .a1).toNat = 24) → post s s'
  pub := modePub

section
variable {post : State → State → Prop} {s s₁ : State} (hs : (finalContract post).pre s) (h₁ : Shifted s s₁)
include hs

theorem roundsF_of : rounds s = 18 ∨ rounds s = 24 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hn⟩ := hs
  exact hn

include h₁

theorem seqPreF_of (d : Dir) (R : Nat) : SeqPre (dirCore d R) byteMode s₁ := by
  obtain ⟨-, hwr, -, -, dVD, -, fV, fD, al, sp, -, dSV, dSD, -⟩ := hs
  have eS : Proof.Modes.RISCV64.scrRegion (dirCore d R) (Proof.Modes.RISCV64.Fb s₁ (dirCore d R)) =
      ⟨s.sp - frameBytes, frameBytes⟩ := by
    simp only [Proof.Modes.RISCV64.scrRegion, Proof.Modes.RISCV64.Fb, h₁.sp]; rfl
  have eV : Proof.Modes.RISCV64.ivR s₁ (dirCore d R) = ⟨s.gpr .a2, 16⟩ := by
    simp only [Proof.Modes.RISCV64.ivR, Proof.Modes.RISCV64.P, h₁.a1]; rfl
  have eD : Proof.Modes.RISCV64.dataRegion (Proof.Modes.RISCV64.Dp s₁) byteMode.step (Proof.Modes.RISCV64.N s₁) =
      ⟨s.gpr .a3, (s.gpr .a4).toNat⟩ := by
    simp only [Proof.Modes.RISCV64.dataRegion, Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, h₁.a2, h₁.a3,
      byteMode, Nat.one_mul]
  have hwr₁ : s₁.wr = [⟨s.gpr .a2, 16⟩, ⟨s.gpr .a3, (s.gpr .a4).toNat⟩] := by rw [h₁.wr, hwr]
  refine ⟨by rw [h₁.sp]; exact al, by rw [h₁.sp]; exact sp, by rw [eV, hwr₁]; simp,
    fun _ => by rw [eV, hwr₁]; simp,
    by simp only [Proof.Modes.RISCV64.P, h₁.a1]; exact fV, by rw [eD, hwr₁]; simp,
    by simp only [Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, h₁.a2, h₁.a3, byteMode, Nat.one_mul]; exact fD,
    by rw [eD, eS]; exact dSD.symm, by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, eD]; exact dVD,
    ⟨by decide, by rw [bw_eq]; decide⟩, layout d R⟩

theorem keyArgsF_of (d : Dir) (R : Nat) :
    KeyArgs R s₁ (Proof.Modes.RISCV64.wrs0 (dirCore d R) byteMode s₁) (schedWords s.mem (s.gpr .a0) R) := by
  obtain ⟨hrd, -, -, dKD, -, fK, -, -, -, -, dSK, -, -, -⟩ := hs
  have ews : Proof.Modes.RISCV64.wrs0 (dirCore d R) byteMode s₁ =
      [⟨s.gpr .a3, (s.gpr .a4).toNat⟩, ⟨s.sp - frameBytes, frameBytes⟩] := by
    simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, Proof.Modes.RISCV64.dataRegion,
      Proof.Modes.RISCV64.scrRegion, Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, Proof.Modes.RISCV64.Fb,
      h₁.a2, h₁.a3, h₁.sp, byteMode, Nat.one_mul]
    rfl
  refine ⟨s.gpr .a0, h₁.a0, by rw [h₁.mem], by rw [h₁.rd, hrd]; simp, fK, fun r hr => ?_⟩
  rw [ews] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact dKD
  · exact dSK.symm

end

/-- The final functions' arguments from the modes' proof, in the functions'
terms. -/
theorem argsF_eq {s s₁ : State} (h₁ : Shifted s s₁) :
    Proof.Modes.RISCV64.P s₁ = s.gpr .a2 ∧ Proof.Modes.RISCV64.Dp s₁ = s.gpr .a3 ∧
      Proof.Modes.RISCV64.N s₁ = (s.gpr .a4).toNat :=
  ⟨h₁.a1, h₁.a2, by simp only [Proof.Modes.RISCV64.N, h₁.a3]⟩

theorem cfbEncryptFinal_correct (s : State) (hs : (finalContract encFinalPost).pre s) :
    ∃ t s', Exec isa cfbEncryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract encFinalPost).post s s' := by
  refine modeFn_wp (roundsF_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cfbEncFinal_wp
    (dirCoreSpec .encrypt _ (roundsF_of hs)) (seqPreF_of hs h₁ .encrypt _) (keyArgsF_of hs h₁ .encrypt _))
    fun s' ⟨h1, h2, _⟩ => ⟨h₁.abi h1, fun _ => ?_⟩
  obtain ⟨e1, e2, e3⟩ := argsF_eq h₁
  rw [bw_eq, cipher_enc, e1, e2, e3, h₁.mem] at h2
  exact h2

theorem cfbDecryptFinal_correct (s : State) (hs : (finalContract decFinalPost).pre s) :
    ∃ t s', Exec isa cfbDecryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract decFinalPost).post s s' := by
  refine modeFn_wp (roundsF_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cfbDecFinal_wp
    (dirCoreSpec .encrypt _ (roundsF_of hs)) (seqPreF_of hs h₁ .encrypt _) (keyArgsF_of hs h₁ .encrypt _))
    fun s' ⟨h1, h2, _⟩ => ⟨h₁.abi h1, fun _ => ?_⟩
  obtain ⟨e1, e2, e3⟩ := argsF_eq h₁
  rw [bw_eq, cipher_enc, e1, e2, e3, h₁.mem] at h2
  exact h2

theorem ofbFinal_correct (s : State) (hs : (finalContract ofbFinalPost).pre s) :
    ∃ t s', Exec isa ofbFinal s t s' ∧ abiPreserved s s' ∧ (finalContract ofbFinalPost).post s s' := by
  refine modeFn_wp (roundsF_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.ofbFinal_wp
    (dirCoreSpec .encrypt _ (roundsF_of hs)) (seqPreF_of hs h₁ .encrypt _) (keyArgsF_of hs h₁ .encrypt _))
    fun s' ⟨h1, h2, _⟩ => ⟨h₁.abi h1, fun _ => ?_⟩
  obtain ⟨e1, e2, e3⟩ := argsF_eq h₁
  rw [bw_eq, cipher_enc, e1, e2, e3, h₁.mem] at h2
  exact h2

/-! ## Constant time -/

theorem cfbEncryptFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncryptFinal :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbDecryptFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecryptFinal :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem ofbFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofbFinal :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

/-! ## The contracts -/

theorem cfbEncryptFinal_verified :
    Verified RISCV64.target cfbEncryptFinal (Spec.Camellia.cfbEncryptFinalContract RISCV64.abi frameBytes) :=
  Proof.Camellia.cfbEncryptFinal_of_sk <| by
  refine Verified.of_correct cfbEncryptFinal_correct (cfbEncryptFinal_constantTime _) ?_
  contract_implies [Proof.Camellia.cfbEncryptFinalContractSk, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre,
    Proof.Camellia.cfbEncryptFinalPostSk, RISCV64.abi, RISCV64.argRegs, finalContract, encFinalPost, modePub_iff]
    [modeSat] using modeSat

theorem cfbDecryptFinal_verified :
    Verified RISCV64.target cfbDecryptFinal (Spec.Camellia.cfbDecryptFinalContract RISCV64.abi frameBytes) :=
  Proof.Camellia.cfbDecryptFinal_of_sk <| by
  refine Verified.of_correct cfbDecryptFinal_correct (cfbDecryptFinal_constantTime _) ?_
  contract_implies [Proof.Camellia.cfbDecryptFinalContractSk, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre,
    Proof.Camellia.cfbDecryptFinalPostSk, RISCV64.abi, RISCV64.argRegs, finalContract, decFinalPost, modePub_iff]
    [modeSat] using modeSat

theorem ofbFinal_verified :
    Verified RISCV64.target ofbFinal (Spec.Camellia.ofbFinalContract RISCV64.abi frameBytes) :=
  Proof.Camellia.ofbFinal_of_sk <| by
  refine Verified.of_correct ofbFinal_correct (ofbFinal_constantTime _) ?_
  contract_implies [Proof.Camellia.ofbFinalContractSk, Spec.Camellia.ofbFinalSig, Spec.Camellia.ofbFinalPre,
    Proof.Camellia.ofbFinalPostSk, RISCV64.abi, RISCV64.argRegs, finalContract, ofbFinalPost, modePub_iff]
    [modeSat] using modeSat

end VG.Proof.Camellia.RISCV64.Modes
