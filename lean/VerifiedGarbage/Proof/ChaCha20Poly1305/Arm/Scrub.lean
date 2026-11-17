module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Verified
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Lit

/-!
# ChaCha20-Poly1305 on ARMv7, without secret residue

`seal`, `open` and `open_to`, with either arithmetic of Poly1305 (`umaal`),
keep their working space in a frame, which they wipe. Their postconditions
read the memory on return only within the data, the tag and the destination
(`Arm.Scrub.PostOut`; `open_to`'s where its precondition holds), so each is
registered followed by a wipe of all the stack its contract reserves
(`Arm.Scrub.scrubRegF`), and by instructions that set the registers a callee
may change, but the result, and the flags to constants.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack
open VG.Impl.ChaCha20Poly1305.Arm

/-- `Arm.Scrub.postOut_of_local`, for a postcondition that reads the memory
on return only within the buffers where the precondition holds (one that
reads an output buffer by a length the precondition equates with the
buffer's). -/
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

/-- `seal`'s postcondition reads the memory on return only within the
buffers: the data and the tag. -/
theorem sealOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.sealContract abi stack) (Spec.ChaCha20Poly1305.sealSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (sealPost_out _)

theorem openOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openZeroContract abi stack) (Spec.ChaCha20Poly1305.openSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (openZeroPost_out _)

theorem openToOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openToContract abi stack) (Spec.ChaCha20Poly1305.openToSig.retBits 32) :=
  postOut_of_local_pre ScrubAbi.plain (openToPost_out _)

theorem frameOk_664 : FrameOk 664 := by decide

theorem frameOk_672 : FrameOk 672 := by decide

theorem seal_armStack (umaal : Bool) :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 («seal» umaal)) ≤ 664 := by
  cases umaal <;> lit_decide

theorem open_armStack (umaal : Bool) :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 («open» umaal)) ≤ 664 := by
  cases umaal <;> lit_decide

theorem openTo_armStack (umaal : Bool) :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 664 5 158 (openTo umaal)) ≤ 672 := by
  cases umaal <;> lit_decide

theorem seal_noIcall (umaal : Bool) :
    noIcall (Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 («seal» umaal)) = true := by
  cases umaal <;> lit_decide

def sealReg (umaal : Bool) (suffix : String) : Registration Spec.ChaCha20Poly1305.sealApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 («seal» umaal)
      verified := seal_framed }
    (seal_armStack umaal) (seal_noIcall umaal) frameOk_664 (sealOut _) rfl

theorem open_noIcall (umaal : Bool) :
    noIcall (Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 («open» umaal)) = true := by
  cases umaal <;> lit_decide

def openReg (umaal : Bool) (suffix : String) : Registration Spec.ChaCha20Poly1305.openZeroApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 («open» umaal)
      verified := open_framed }
    (open_armStack umaal) (open_noIcall umaal) frameOk_664 (openOut _) rfl

theorem openTo_noIcall (umaal : Bool) :
    noIcall (Impl.StackScratch.Arm.withStackScratchWiped 664 5 158 (openTo umaal)) = true := by
  cases umaal <;> lit_decide

def openToReg (umaal : Bool) (suffix : String) : Registration Spec.ChaCha20Poly1305.openToApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := Impl.StackScratch.Arm.withStackScratchWiped 664 5 158 (openTo umaal)
      verified := openTo_framed }
    (openTo_armStack umaal) (openTo_noIcall umaal) frameOk_672 (openToOut _) rfl

/-! ## `seal`, as `seal_gather` calls it -/

/-- `vg_chacha20_poly1305_seal`'s code, as its registration emits it
(`sealReg`): with its working space in a frame, and scrubbed. -/
def sealCode (umaal : Bool) : Prog isa :=
  scrubF 0 664 (Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 («seal» umaal))

theorem sealCode_eq (umaal : Bool) (suffix : String) : (sealReg umaal suffix).code = sealCode umaal := rfl

theorem sealCode_verified (umaal : Bool) :
    Verified Arm.target (sealCode umaal) (Spec.ChaCha20Poly1305.sealContract Arm.abi 664) :=
  (sealReg umaal "").verified

theorem sealCode_armStack (umaal : Bool) : armStack (sealCode umaal) ≤ 664 := by
  cases umaal <;> lit_decide

end VG.Proof.ChaCha20Poly1305.Arm.Scrub
