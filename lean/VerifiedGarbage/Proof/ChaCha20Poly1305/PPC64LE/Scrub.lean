module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.GatherOut
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ChaCha20-Poly1305 on PPC64LE, without secret residue

`vg_chacha20_poly1305_seal`, `vg_chacha20_poly1305_open`,
`vg_chacha20_poly1305_open_to` and `vg_chacha20_poly1305_seal_gather`, each
followed by `Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.scrubOf`), which
clears every volatile register and the stack their frames used: they zero
their working space themselves (`withStackScratchWiped`,
`withStackScratchArgsWiped`), but not the 160-byte frame below it in which
they run Poly1305's block function (`withStackScratch`), nor the rest of
`open_to`'s frame and `seal_gather`'s.
`seal_gather` calls `seal`'s code as the internal
`vg_chacha20_poly1305_seal_core`
(`Impl.ChaCha20Poly1305.PPC64LE.SealGather.sealGather`), since the exported
one now clears its stack. Their postconditions read the memory on return
only within the data and the tag, by RISC-V's proofs
(`Proof/ChaCha20Poly1305/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.ChaCha20Poly1305

/-! ## Postconditions -/

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers when the precondition holds (RISC-V's
`RISCV64.Scrub.postOut_of_local_pre`). -/
theorem postOut_of_local_pre {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      Curry.apply (sig.words A.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -, -, -, hpre⟩ := hs
    have hpre' : Curry.apply (sig.words A.ptrBits) pre (vals s) (A.mem s) := by
      cases hal : A.alignsBufs
      · rw [hal] at hpre; exact hpre
      · rw [hal] at hpre; exact hpre.1
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hA.mem] at hpre'
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) hpre' (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

theorem sealOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.sealContract PPC64LE.abi stack) (Spec.ChaCha20Poly1305.sealSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (sealPost_out _)

theorem openOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openZeroContract PPC64LE.abi stack) (Spec.ChaCha20Poly1305.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (openZeroPost_out _)

theorem openToOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openToContract PPC64LE.abi stack) (Spec.ChaCha20Poly1305.openToSig.retBits 64) :=
  postOut_of_local_pre ScrubAbi.plain (openToPost_out _)

theorem gatherOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.sealGatherContract PPC64LE.abi stack)
      (Spec.ChaCha20Poly1305.sealGatherSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (Proof.ChaCha20Poly1305.sealGatherPost_out _)

/-! ## The registrations -/

/-- `Spec.ChaCha20Poly1305.sealApi`. -/
def sealReg : Registration Spec.ChaCha20Poly1305.sealApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 688 .r10 82
        (Impl.ChaCha20Poly1305.PPC64LE.inPlace Impl.ChaCha20Poly1305.PPC64LE.«seal»)
      verified := Proof.ChaCha20Poly1305.PPC64LE.seal_framed }
    848 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9,
       .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (sealOut _)
    (by dsimp only; lit_decide)

/-- `Spec.ChaCha20Poly1305.openZeroApi`. -/
def openReg : Registration Spec.ChaCha20Poly1305.openZeroApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 688 .r10 82
        (Impl.ChaCha20Poly1305.PPC64LE.inPlace Impl.ChaCha20Poly1305.PPC64LE.«open»)
      verified := Proof.ChaCha20Poly1305.PPC64LE.open_framed }
    848 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9,
       .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (openOut _)
    (by dsimp only; lit_decide)

/-- `Spec.ChaCha20Poly1305.openToApi`. -/
def openToReg : Registration Spec.ChaCha20Poly1305.openToApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchArgsWiped 768 1 82 Impl.ChaCha20Poly1305.PPC64LE.openTo
      verified := Proof.ChaCha20Poly1305.PPC64LE.openTo_framed }
    928 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9,
       .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (openToOut _)
    (by dsimp only; lit_decide)

/-- `Spec.ChaCha20Poly1305.sealGatherApi`. -/
def sealGatherReg : Registration Spec.ChaCha20Poly1305.sealGatherApi PPC64LE.target :=
  scrubOf {
      code := Impl.ChaCha20Poly1305.PPC64LE.SealGather.sealGather
      verified := Proof.ChaCha20Poly1305.PPC64LE.Gather.sealGather_verified }
    928 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9,
       .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (gatherOut _)
    (by dsimp only; lit_decide)

end VG.Proof.ChaCha20Poly1305.PPC64LE.Scrub
