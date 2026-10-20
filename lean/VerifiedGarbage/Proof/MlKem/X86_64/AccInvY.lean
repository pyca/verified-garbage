module

public import VerifiedGarbage.Proof.MlKem.X86_64.AccY
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvTop
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAccA
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc0
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc1

/-!
# ML-KEM on x86-64: `NTT⁻¹` of the AVX2 accumulator

`nttInvAccY` (`Impl/MlKem/X86_64/KpkeAccY.lean`) is `NTT⁻¹` on registers
reading the accumulator (`NttR.nttIR_ok`, with `NttR.checkI_acc`).
`accIdx_add32` and `acc_word` are the accumulator's order and words, which
`FinY.lean` reads.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem accIdx_add32 {u w : Nat} (hw : w < 32) : accIdx (32 * u + w) = 32 * u + accIdx w := by
  unfold accIdx; omega

/-- Word `e` of 16 bytes loaded from `wAddr p j + 32h + 16l`. -/
theorem acc_word (m : Mem) (p : Addr) (j h l : Nat) {e : Nat} (he : e < 8) :
    word (m.readW (wAddr p j + BitVec.ofNat 64 (32 * h) + BitVec.ofNat 64 (16 * l)) 128) e =
      wordAt m p (j + 16 * h + 8 * l + e) := by
  rw [word_readW _ _ he, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
    show 32 * h + (16 * l + 2 * e) = 2 * (16 * h + 8 * l + e) by omega, wAddr_add, ← wordAt]
  exact congrArg _ (by omega)

theorem nttInvAccY_correct (s : State) (hs : (invAccK accY).pre s) :
    ∃ t s', Exec isa nttInvAccY s t s' ∧ abiPreserved s s' ∧ (invAccK accY).post s s' := by
  obtain ⟨F0, hF0⟩ := hs.2.2.2.2.2
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa nttInvAccY s fun s' => PolyIs s'.mem (s.gpr .rdi) (nttInv F0) ∧
      Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem :=
    WP.mono (NttR.nttIR_ok NttR.checkI_acc hw hwf hd (src := .acc) hF0) fun _ ⟨hP, hf, _⟩ => ⟨hP, hf⟩
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep [.rax, .r8] hW (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he
    (gprPreserved_of hk (by decide) hf (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)),
    fun F hF => by rw [acc16_unique hF hF0]; exact hP⟩

end VG.Proof.MlKem.X86_64
