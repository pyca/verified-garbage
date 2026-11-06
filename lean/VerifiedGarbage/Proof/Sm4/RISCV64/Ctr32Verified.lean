module

public import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
public import VerifiedGarbage.Spec.Sm4.Gcm
public import VerifiedGarbage.Proof.Sm4.Contract
meta import VerifiedGarbage.Proof.Sm4.Contract
import VerifiedGarbage.Proof.Modes.RISCV64.WideCtr
import VerifiedGarbage.Proof.Modes.Ctr32
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
meta import VerifiedGarbage.Spec.Sm4.Gcm

/-!
# SM4's counter mode with GCM's `inc₃₂` on RISC-V meets its contract

`ctr32_correct`: the counter mode of `Proof/Modes/RISCV64/WideCtr.lean`,
sixteen blocks a step while sixteen are left (`ctr32Wide_wp`), over
SM4's core (`dirCoreSpec .encrypt`) is correct (`ctr32Post`) with the
modes' frame of 3232 bytes below the stack pointer (`modeContract`). As on
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
  WP.mono (Proof.Modes.RISCV64.ctr32Wide_wp (lg := 4) (dirCoreSpec .encrypt) rfl (by decide)
    (by exact (by decide : 2 ^ 4 ≤ 16)) (by decide)
    (seqPre_of .encrypt (M := Mode.ctr32Early) rfl hs)
    (keyArgs_of .encrypt (M := Mode.ctr32Early) rfl hs))
    fun _ ⟨h1, h2, h3, _⟩ => by
      simp only [cipher_enc] at h2 h3
      refine ⟨h1, ?_, h3⟩
      rw [Proof.Modes.gcmBlocks_eq, Proof.Modes.gcmBlocks_eq]
      exact h2

end VG.Proof.Sm4.RISCV64.Modes
