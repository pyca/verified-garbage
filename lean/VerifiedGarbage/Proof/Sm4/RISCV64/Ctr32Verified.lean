module

public import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
public import VerifiedGarbage.Spec.Sm4.Gcm
public import VerifiedGarbage.Proof.Sm4.Contract
meta import VerifiedGarbage.Proof.Sm4.Contract
import VerifiedGarbage.Proof.Modes.RISCV64.Ctr32
import VerifiedGarbage.Proof.Modes.Ctr32
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
meta import VerifiedGarbage.Spec.Sm4.Gcm

/-!
# SM4's counter mode with GCM's `inc₃₂` on RISC-V meets its contract

`ctr32_verified`: the counter mode of `Proof/Modes/RISCV64/Ctr32.lean` over
SM4's core (`dirCoreSpec .encrypt`) meets `vg_sm4_ctr32`'s contract with the
modes' frame of 3232 bytes below the stack pointer (`modeContract`), and is
constant time as the other modes are (`ModesConstantTime.lean`). As on
PPC64LE (`Proof/Sm4/PPC64LE/Ctr32Verified.lean`), whose working space is an
argument instead.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64.Modes

open VG VG.RISCV64 VG.Impl.Sm4.RISCV64 VG.Impl.Modes
open VG.Proof.Sm4.RISCV64.Mode (dirCoreSpec)
open VG.Proof.Sm4.RISCV64 (modePub)

/-- The data XORed with the encrypted counter blocks, and `inc₃₂ⁿ` of the
counter block, as GCM's blocks. -/
def ctr32Post (s s' : State) : Prop :=
  Spec.Gcm.blocksAt s'.mem (s.gpr .a2) (s.gpr .a3).toNat =
      Spec.Gcm.ctr32 (Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s.mem (s.gpr .a0)))
        (Spec.Gcm.blockAt s.mem (s.gpr .a1)) (Spec.Gcm.blocksAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) ∧
    Spec.Gcm.blockAt s'.mem (s.gpr .a1) =
      Nat.repeat Spec.Gcm.inc32 (s.gpr .a3).toNat (Spec.Gcm.blockAt s.mem (s.gpr .a1))

theorem ctr32_correct (s : State) (hs : (modeContract ctr32Post).pre s) :
    ∃ t s', Exec isa ctr32 s t s' ∧ abiPreserved s s' ∧ (modeContract ctr32Post).post s s' :=
  WP.mono (Proof.Modes.RISCV64.ctr32_wp (dirCoreSpec .encrypt) rfl
    (seqPre_of .encrypt (M := Mode.ctr32) rfl hs)
    (keyArgs_of .encrypt (M := Mode.ctr32) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [cipher_enc] at h2 h3
      refine ⟨h1, ?_, h3⟩
      rw [Proof.Modes.gcmBlocks_eq, Proof.Modes.gcmBlocks_eq]
      exact h2

theorem ctr32_verified : Verified RISCV64.target ctr32 (Proof.Sm4.ctr32Contract RISCV64.abi frameBytes) := by
  refine Verified.of_correct ctr32_correct (Proof.Sm4.RISCV64.ctr32_constantTime _) ?_
  contract_implies [Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, RISCV64.abi, RISCV64.argRegs,
    modeContract, ctr32Post, modePub_iff] [modeSat] using modeSat

end VG.Proof.Sm4.RISCV64.Modes
