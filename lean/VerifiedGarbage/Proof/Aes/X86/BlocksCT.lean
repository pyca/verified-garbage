import VerifiedGarbage.Proof.Aes.X86.Blocks
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Spec.Aes.Contract

/-!
# AES on whole blocks on x86 (32-bit): constant time, and `Verified`

The taint analysis (`VG.X86.Taint`) starts with `esp` public and knows
where the arguments are and which of them are the base addresses of the
data and the scratch buffer. As in `vg_aes_ctr32` (`Ctr32CT.lean`), the data
pointer and the count round-trip through public slots of the scratch
buffer; the stores of the blocks through the data pointer forget them, and
the code stores them again from the registers.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86

def blocksτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 2048], argLen := 24,
    argBases := [(12, 0), (20, 1)] }

theorem blocks_wf₀ {s : State} (hp : BPre s) : VG.X86.Taint.Wf blocksτ₀ s := by
  have hD := hp.fD; have hB := hp.fB; have hs := hp.fSp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [blocksτ₀]; omega, ?_⟩, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.dDB, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [toNat_setWidth32] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.rD hp.aD
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.rB hp.aB
  · intro p hp'
    simp only [blocksτ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem blocks_agree₀ {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₁ s₂ : State}
    (h₁ : (Proof.Aes.blocksX86 f).pre s₁) (h₂ : (Proof.Aes.blocksX86 f).pre s₂)
    (hpub : (Proof.Aes.blocksX86 f).pub s₁ s₂) : VG.X86.Taint.Agree blocksτ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := BPre.of h₁; have hp₂ := BPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, blocks_wf₀ hp₁, blocks_wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [blocksτ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [bDatR, bScrR, bDatP, bN, bScrP, ha 2 (by omega), ha 3 (by omega), ha 4 (by omega)]
  · simp only [blocksτ₀] at hk
    rw [show VG.X86.Taint.depth blocksτ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 24) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 24) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.cipher).pub Impl.Aes.X86.encryptBlocks :=
  VG.Taint.constantTime (A := VG.X86.taint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.invCipher).pub Impl.Aes.X86.decryptBlocks :=
  VG.Taint.constantTime (A := VG.X86.taint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

/-- Memory holding the arguments `0x1000, 10, 0x3000, 0, 0x4000` at `0x8004`. -/
def blocksSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800D then 0x30
  else if a = 0x8015 then 0x40 else 0

/-- A state satisfying the precondition (with no data). -/
def blocksSat : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := blocksSatMem
  rd := [⟨0x1000, 240⟩, ⟨0x8004, 20⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2048⟩]

theorem encryptBlocks_verified :
    Verified X86.target Impl.Aes.X86.encryptBlocks (Spec.Aes.encryptBlocksContract X86.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct
    (by
      have a0 : arg blocksSat 0 = 0x1000 := by decide
      have a1 : arg blocksSat 1 = 10 := by decide
      have a2 : arg blocksSat 2 = 0x3000 := by decide
      have a3 : arg blocksSat 3 = 0 := by decide
      have a4 : arg blocksSat 4 = 0x4000 := by decide
      have e : argAddr blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat)

theorem decryptBlocks_verified :
    Verified X86.target Impl.Aes.X86.decryptBlocks (Spec.Aes.decryptBlocksContract X86.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct
    (by
      have a0 : arg blocksSat 0 = 0x1000 := by decide
      have a1 : arg blocksSat 1 = 10 := by decide
      have a2 : arg blocksSat 2 = 0x3000 := by decide
      have a3 : arg blocksSat 3 = 0 := by decide
      have a4 : arg blocksSat 4 = 0x4000 := by decide
      have e : argAddr blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat)

end VG.Proof.Aes.X86
