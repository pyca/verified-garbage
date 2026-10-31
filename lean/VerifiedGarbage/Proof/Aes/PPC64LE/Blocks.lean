module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Base
public import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Blocks
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

meta import VerifiedGarbage.Proof.Aes.PPC64LE.Base
meta import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Blocks
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

/-! # Baseline POWER8 AES block contracts -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE
open VG VG.PPC64LE
open VG.Impl.Aes.PPC64LE (encryptBlocks decryptBlocks)

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksPPC64LE Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksPPC64LE Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, hk, hp⟩ := Crypto.blocks_ok false s hs
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), hp⟩

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksPPC64LE Spec.Aes.cipher).pre
    (Proof.Aes.blocksPPC64LE Spec.Aes.cipher).pub encryptBlocks := by
  refine VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksPPC64LE Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksPPC64LE Spec.Aes.invCipher).post s s' := by
  obtain ⟨t, s', he, hk, hp⟩ := Crypto.blocks_ok true s hs
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), hp⟩

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksPPC64LE Spec.Aes.invCipher).pre
    (Proof.Aes.blocksPPC64LE Spec.Aes.invCipher).pub decryptBlocks := by
  refine VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (one block). -/
def blocksSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x3000 | .r6 => 1 | .r7 => 0x4000
    | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 2048⟩]

theorem encryptBlocks_verified :
    Verified PPC64LE.target encryptBlocks (Spec.Aes.encryptBlocksContract PPC64LE.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct (by
    sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksPPC64LE,
      PPC64LE.abi, PPC64LE.argRegs] [blocksSat] using blocksSat)

theorem decryptBlocks_verified :
    Verified PPC64LE.target decryptBlocks (Spec.Aes.decryptBlocksContract PPC64LE.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct (by
    sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksPPC64LE,
      PPC64LE.abi, PPC64LE.argRegs] [blocksSat] using blocksSat)


end VG.Proof.Aes.PPC64LE
