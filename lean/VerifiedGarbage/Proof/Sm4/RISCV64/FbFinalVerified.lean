module

public import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
public import VerifiedGarbage.Impl.Sm4.RISCV64.FbFinal
public import VerifiedGarbage.Spec.Sm4.CfbFinal
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sm4.RISCV64.FbFinalLit
meta import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
meta import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
meta import VerifiedGarbage.Impl.Sm4.RISCV64.FbFinal
meta import VerifiedGarbage.Spec.Sm4.CfbFinal
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sm4.RISCV64.FbFinalLit

/-!
# SM4-CFB128 of a message's last piece on RISC-V meets its contracts

The modes' CFB over a message's last piece (`Proof.Modes.RISCV64.cfbEncFinal_wp`,
`cfbDecFinal_wp`) over Sm4's one-block encryption core meets the contracts,
with `stack := 3232`, that core's frame (`ModesVerified.lean`), whose
precondition, with the data `len` bytes, is `seq`'s for the data a byte at a
time (`byteMode`). Constant time as the whole-block functions.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64.Modes

open VG VG.RISCV64 VG.Impl.Sm4.RISCV64 VG.Impl.Modes
open VG.Proof.Modes.RISCV64 (SeqPre ivR scrRegion Fb byteMode)
open VG.Proof.Sm4.RISCV64.Mode (dirCoreSpec KeyArgs layout)
open VG.Proof.Sm4.RISCV64 (modePub modes_ofRegs)

/-- The final functions' postconditions. -/
def encFinalPost (s s' : State) : Prop :=
  Spec.Cfb.EncryptFinal (ciph s) 16 s.mem s'.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3).toNat
def decFinalPost (s s' : State) : Prop :=
  Spec.Cfb.DecryptFinal (ciph s) 16 s.mem s'.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3).toNat

/-- A final function on RISC-V, with its frame below the stack pointer, the
data `len` bytes, and the postcondition `post`. -/
def finalContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 128⟩
    let iv : Region := ⟨s.gpr .a1, 16⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes, frameBytes⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a0).toNat + 128 ≤ 2 ^ 64 ∧
      (s.gpr .a1).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data
  post := post
  pub := modePub

theorem seqPreF_of {post : State → State → Prop} {s : State} (h : (finalContract post).pre s) :
    SeqPre (dirCore .encrypt) byteMode s := by
  obtain ⟨-, hwr, -, -, dVD, -, fV, fD, al, sp, -, dSV, dSD⟩ := h
  have eb : 4 * (dirCore .encrypt).bw = 16 := rfl
  have eS := (show scrRegion (dirCore .encrypt) (Fb s (dirCore .encrypt)) = ⟨s.sp - frameBytes, frameBytes⟩ from rfl)
  have eV : ivR s (dirCore .encrypt) = ⟨s.gpr .a1, 16⟩ := rfl
  have eD : Proof.Modes.RISCV64.dataRegion (s.gpr .a2) byteMode.step (s.gpr .a3).toNat =
      ⟨s.gpr .a2, (s.gpr .a3).toNat⟩ := by
    simp only [Proof.Modes.RISCV64.dataRegion, byteMode, Nat.one_mul]
  refine ⟨al, sp, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp, by rw [eb]; exact fV,
    by rw [eD, hwr]; simp, by simp only [byteMode, Nat.one_mul]; exact fD, by rw [eD, eS]; exact dSD.symm,
    by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, eD]; exact dVD, ⟨by decide, by rw [eb]; decide⟩,
    Mode.layout .encrypt⟩

theorem keyArgsF_of {post : State → State → Prop} {s : State} (h : (finalContract post).pre s) :
    KeyArgs s (Proof.Modes.RISCV64.wrs0 (dirCore .encrypt) byteMode s) (Spec.Sm4.scheduleAt s.mem (s.gpr .a0)) := by
  obtain ⟨hrd, -, -, dKD, -, fK, -, -, -, -, dSK, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fK, fun r hr => ?_⟩
  simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .a0) 128).Disjoint ⟨s.gpr .a2, 1 * (s.gpr .a3).toNat⟩
    rw [Nat.one_mul]; exact dKD
  · exact dSK.symm

theorem cfbEncryptFinal_correct (s : State) (hs : (finalContract encFinalPost).pre s) :
    ∃ t s', Exec isa cfbEncryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract encFinalPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbEncFinal_wp (dirCoreSpec .encrypt) (seqPreF_of hs) (keyArgsF_of hs))
    fun _ ⟨h1, h2, _⟩ => ⟨h1, h2⟩

theorem cfbDecryptFinal_correct (s : State) (hs : (finalContract decFinalPost).pre s) :
    ∃ t s', Exec isa cfbDecryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract decFinalPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbDecFinal_wp (dirCoreSpec .encrypt) (seqPreF_of hs) (keyArgsF_of hs))
    fun _ ⟨h1, h2, _⟩ => ⟨h1, h2⟩

/-! ## Constant time -/

theorem cfbEncryptFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncryptFinal :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbDecryptFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecryptFinal :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

/-! ## The contracts -/

theorem cfbEncryptFinal_verified :
    Verified RISCV64.target cfbEncryptFinal (Spec.Sm4.cfbEncryptFinalContract RISCV64.abi (frameBytes)) := by
  refine Verified.of_correct cfbEncryptFinal_correct (cfbEncryptFinal_constantTime _) ?_
  contract_implies [Spec.Sm4.cfbEncryptFinalContract, Spec.Sm4.cfbFinalSig, RISCV64.abi,
    RISCV64.argRegs, finalContract, encFinalPost, modePub_iff] [modeSat] using modeSat

theorem cfbDecryptFinal_verified :
    Verified RISCV64.target cfbDecryptFinal (Spec.Sm4.cfbDecryptFinalContract RISCV64.abi (frameBytes)) := by
  refine Verified.of_correct cfbDecryptFinal_correct (cfbDecryptFinal_constantTime _) ?_
  contract_implies [Spec.Sm4.cfbDecryptFinalContract, Spec.Sm4.cfbFinalSig, RISCV64.abi,
    RISCV64.argRegs, finalContract, decFinalPost, modePub_iff] [modeSat] using modeSat

end VG.Proof.Sm4.RISCV64.Modes
