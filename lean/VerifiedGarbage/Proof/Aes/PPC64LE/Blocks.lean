module

public import VerifiedGarbage.Proof.Aes.Rounds
public import VerifiedGarbage.Proof.Aes.PPC64LE.Base
public import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Blocks
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.Offset

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
  obtain ⟨t, s', he, hk, -, hp⟩ := Crypto.blocks_ok false s hs
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
  obtain ⟨t, s', he, hk, -, hp⟩ := Crypto.blocks_ok true s hs
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

theorem encryptBlocks_implies :
    (Proof.Aes.blocksPPC64LE Spec.Aes.cipher).Implies (Proof.Aes.encryptBlocksRoundsContract PPC64LE.abi) := by
  sig_implies [Proof.Aes.encryptBlocksRoundsContract, Spec.Aes.blocksSig, Proof.Aes.blocksPPC64LE,
    PPC64LE.abi, PPC64LE.argRegs] [blocksSat] using blocksSat

theorem decryptBlocks_implies :
    (Proof.Aes.blocksPPC64LE Spec.Aes.invCipher).Implies (Proof.Aes.decryptBlocksRoundsContract PPC64LE.abi) := by
  sig_implies [Proof.Aes.decryptBlocksRoundsContract, Spec.Aes.blocksSig, Proof.Aes.blocksPPC64LE,
    PPC64LE.abi, PPC64LE.argRegs] [blocksSat] using blocksSat

theorem encryptBlocks_verified :
    Verified PPC64LE.target encryptBlocks (Proof.Aes.encryptBlocksRoundsContract PPC64LE.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct encryptBlocks_implies

theorem decryptBlocks_verified :
    Verified PPC64LE.target decryptBlocks (Proof.Aes.decryptBlocksRoundsContract PPC64LE.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct decryptBlocks_implies

/-- The blocks functions' contract, with the frame of their proofs: only
the data changes. -/
def blocksFramed (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract isa where
  pre := (Proof.Aes.blocksPPC64LE f).pre
  post s s' := (Proof.Aes.blocksPPC64LE f).post s s' ∧
    Frame [⟨s.gpr .r5, 16 * (s.gpr .r6).toNat⟩] s.mem s'.mem
  pub := (Proof.Aes.blocksPPC64LE f).pub

theorem encryptBlocks_framed (s : State) (hs : (blocksFramed Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧ (blocksFramed Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, hk, hf, hp⟩ := Crypto.blocks_ok false s hs
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), hp, hf⟩

theorem decryptBlocks_framed (s : State) (hs : (blocksFramed Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧ (blocksFramed Spec.Aes.invCipher).post s s' := by
  obtain ⟨t, s', he, hk, hf, hp⟩ := Crypto.blocks_ok true s hs
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), hp, hf⟩

/-- A run of the blocks functions changes no byte of `scratch` (`r7`). -/
theorem blocks_scratch (inverse : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State}
    (hs : (Proof.Aes.blocksPPC64LE f).pre s) {t : List Leak} {s' : State}
    (he : Exec isa (Impl.Aes.PPC64LE.Crypto.blocks inverse) s t s') {i : Nat} (hi : i < 2048) :
    s'.mem (s.gpr .r7 + BitVec.ofNat 64 i) = s.mem (s.gpr .r7 + BitVec.ofNat 64 i) := by
  obtain ⟨t', s'', he', -, hf, -⟩ := Crypto.blocks_ok inverse s hs
  obtain ⟨-, rfl⟩ := Exec.det he he'
  refine hf _ fun r hr hc => ?_
  rw [List.mem_singleton] at hr
  subst hr
  exact hs.2.2.2.2.1 _ hc (Offset.contains_base _ (by omega) (by omega))

theorem encryptBlocks_written (s : State) (t : List Leak) (s' : State)
    (hs : (Proof.Aes.encryptBlocksRoundsContract PPC64LE.abi).pre s) (he : Exec isa encryptBlocks s t s') :
    Sig.writtenWithin (PPC64LE.abi.withConsts []) Spec.Aes.blocksSig [("scratch", 0)] s s' := by
  have hp := encryptBlocks_implies.pre s hs
  simp [Sig.writtenWithin, PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Spec.Aes.blocksSig,
    Sig.words, Sig.arrays, Param.words, ArgWord.bits]
  exact fun i h => blocks_scratch false hp he (by simpa [Elem.size] using h)

theorem decryptBlocks_written (s : State) (t : List Leak) (s' : State)
    (hs : (Proof.Aes.decryptBlocksRoundsContract PPC64LE.abi).pre s) (he : Exec isa decryptBlocks s t s') :
    Sig.writtenWithin (PPC64LE.abi.withConsts []) Spec.Aes.blocksSig [("scratch", 0)] s s' := by
  have hp := decryptBlocks_implies.pre s hs
  simp [Sig.writtenWithin, PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Spec.Aes.blocksSig,
    Sig.words, Sig.arrays, Param.words, ArgWord.bits]
  exact fun i h => blocks_scratch true hp he (by simpa [Elem.size] using h)


end VG.Proof.Aes.PPC64LE
