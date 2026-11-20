module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Gather.Verified
public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86.SealGather
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.GatherOut
import VerifiedGarbage.Proof.ChaCha20.X86.Lit
import VerifiedGarbage.Proof.Poly1305.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Gather.Verified
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.X86.SealGather
meta import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.GatherOut
meta import VerifiedGarbage.Proof.ChaCha20.X86.Lit
meta import VerifiedGarbage.Proof.Poly1305.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# ChaCha20-Poly1305 on x86 (32-bit), without secret residue

`vg_chacha20_poly1305_seal`, `vg_chacha20_poly1305_open`,
`vg_chacha20_poly1305_open_to` and `vg_chacha20_poly1305_seal_gather`, for
each implementation of `vg_chacha20_xor` (`XorImpl`), as emitted
(`Impl.ChaCha20Poly1305.X86.Fn`): their code, then the zeroing of the stack
that their frames and calls use and the clearing of the registers a callee
may change (`X86.Scrub.verifiedScrubbedF`), given that their postconditions
read the memory on return only within the buffers (`sealOut`, …). They call
`vg_poly1305_init`'s code as the internal `vg_poly1305_init_core`, and
`seal_gather` calls `seal`'s as `vg_chacha20_poly1305_seal_core`
(`Gather.sealFn`), since the exported functions now clear their registers
and stack.

What the cleanup needs of their code holds of every implementation
(`seal_scrub`, …): from their code with a stub for the implementation, a
frame of the implementation's 12 bytes around nothing (`holeStub 12`), which
the kernel evaluates here (`seal_side`, …), the implementation's own facts
(`XorImpl.scrub`, `XorImpl.stack`), and `FillB`, which `fillB_calls` proves
by walking only their code. The implementation is called at the deepest
point of their stack, so a budget for the hole (`FillB`), not one added to
the whole (`Fill`), keeps it within the contracts' stack.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86.Scrub

open VG.X86 VG.X86.Scrub
open Impl.StackScratch.X86 (withStackScratchWiped)
open Proof.ChaCha20.X86 (XorImpl)

/-! ## Postconditions -/

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers where the precondition holds (`open_to`'s, which
reads the destination by a length the precondition equates with its
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

theorem sealOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.sealContract X86.abi stack) (Spec.ChaCha20Poly1305.sealSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.ChaCha20Poly1305.sealPost_out _)

theorem openOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openZeroContract X86.abi stack) (Spec.ChaCha20Poly1305.openSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.ChaCha20Poly1305.openZeroPost_out _)

theorem openToOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openToContract X86.abi stack) (Spec.ChaCha20Poly1305.openToSig.retBits 32) :=
  postOut_of_local_pre ScrubAbi.plain (Proof.ChaCha20Poly1305.openToPost_out _)

theorem gatherOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.sealGatherContract X86.abi stack)
      (Spec.ChaCha20Poly1305.sealGatherSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.ChaCha20Poly1305.sealGatherPost_out _)

/-! ## What the cleanup needs of their code -/

/-- An implementation of `vg_chacha20_xor` with no code: a frame of its 12
bytes of stack around nothing. -/
def stub : Impl.ChaCha20.X86.Callee := ⟨"", holeStub 12⟩

-- The functions' own code, with the stub, as literals for the kernel's evaluation.
materialize_code sealStub := withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«seal» stub)
materialize_code openStub := withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«open» stub)
materialize_code openToStub := withStackScratchWiped 748 9 176 (Impl.ChaCha20Poly1305.X86.openTo stub)
materialize_code gatherStub := Impl.ChaCha20Poly1305.X86.SealGather.sealGather "vg_chacha20_poly1305_seal_core"
  (withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«seal» stub))

theorem seal_side :
    scrubFSide (withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«seal» stub)) [] 772 = true := by
  lit_decide

theorem open_side :
    scrubFSide (withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«open» stub)) [] 772 = true := by
  lit_decide

theorem openTo_side :
    scrubFSide (withStackScratchWiped 748 9 176 (Impl.ChaCha20Poly1305.X86.openTo stub)) [] 780 = true := by
  lit_decide

theorem gather_side :
    scrubFSide (Impl.ChaCha20Poly1305.X86.SealGather.sealGather "vg_chacha20_poly1305_seal_core"
      (withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«seal» stub))) [] 824 = true := by
  lit_decide

/-- `scrubFSide` of `vg_chacha20_poly1305_seal`, whatever the implementation. -/
theorem seal_scrub (v : XorImpl) :
    scrubFSide (withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«seal» v.callee)) [] 772 = true := by
  have hc : calleeSide v.callee.code 12 = true := calleeSide_of_eq v.stack v.scrub
  exact scrubFSide_of_fillB (by fillB_calls) seal_side

/-- `scrubFSide` of `vg_chacha20_poly1305_open`, whatever the implementation. -/
theorem open_scrub (v : XorImpl) :
    scrubFSide (withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«open» v.callee)) [] 772 = true := by
  have hc : calleeSide v.callee.code 12 = true := calleeSide_of_eq v.stack v.scrub
  exact scrubFSide_of_fillB (by fillB_calls) open_side

/-- `scrubFSide` of `vg_chacha20_poly1305_open_to`, whatever the implementation. -/
theorem openTo_scrub (v : XorImpl) :
    scrubFSide (withStackScratchWiped 748 9 176 (Impl.ChaCha20Poly1305.X86.openTo v.callee)) [] 780 = true := by
  have hc : calleeSide v.callee.code 12 = true := calleeSide_of_eq v.stack v.scrub
  exact scrubFSide_of_fillB (by fillB_calls) openTo_side

/-- `scrubFSide` of `vg_chacha20_poly1305_seal_gather`, whatever the implementation. -/
theorem gather_scrub (v : XorImpl) :
    scrubFSide (Impl.ChaCha20Poly1305.X86.SealGather.sealGather (Gather.sealFn v).name (Gather.sealFn v).code)
      [] 824 = true := by
  have hc : calleeSide v.callee.code 12 = true := calleeSide_of_eq v.stack v.scrub
  exact scrubFSide_of_fillB (by fillB_calls) gather_side

/-! ## The functions as emitted -/

/-- `vg_chacha20_poly1305_seal`, calling the implementation `v` of `vg_chacha20_xor`, as emitted. -/
theorem seal_scrubbed (v : XorImpl) :
    VerifiedScrubbed target (Impl.ChaCha20Poly1305.X86.Fn.«seal» v.callee)
      (Spec.ChaCha20Poly1305.sealContract X86.abi 772) 0 :=
  verifiedScrubbedF (api := Spec.ChaCha20Poly1305.sealApi)
    { suffix := v.suffix
      code := withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«seal» v.callee)
      stack := 772
      verified := Proof.ChaCha20Poly1305.X86.seal_framed v
      spSafe := Proof.ChaCha20Poly1305.X86.withStackScratchWiped_spSafe
        (Proof.ChaCha20Poly1305.X86.seal_spSafe v) }
    (sealOut _) (hs := seal_scrub v)

/-- `vg_chacha20_poly1305_open`, as emitted. -/
theorem open_scrubbed (v : XorImpl) :
    VerifiedScrubbed target (Impl.ChaCha20Poly1305.X86.Fn.«open» v.callee)
      (Spec.ChaCha20Poly1305.openZeroContract X86.abi 772) 32 :=
  verifiedScrubbedF (api := Spec.ChaCha20Poly1305.openZeroApi)
    { suffix := v.suffix
      code := withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«open» v.callee)
      stack := 772
      verified := Proof.ChaCha20Poly1305.X86.open_framed v
      spSafe := Proof.ChaCha20Poly1305.X86.withStackScratchWiped_spSafe
        (Proof.ChaCha20Poly1305.X86.open_spSafe v) }
    (openOut _) (hs := open_scrub v)

/-- `vg_chacha20_poly1305_open_to`, as emitted. -/
theorem openTo_scrubbed (v : XorImpl) :
    VerifiedScrubbed target (Impl.ChaCha20Poly1305.X86.Fn.openTo v.callee)
      (Spec.ChaCha20Poly1305.openToContract X86.abi 780) 32 :=
  verifiedScrubbedF (api := Spec.ChaCha20Poly1305.openToApi)
    { suffix := v.suffix
      code := withStackScratchWiped 748 9 176 (Impl.ChaCha20Poly1305.X86.openTo v.callee)
      stack := 780
      verified := Proof.ChaCha20Poly1305.X86.openTo_framed v
      spSafe := Proof.ChaCha20Poly1305.X86.withStackScratchWiped_spSafe
        (Proof.ChaCha20Poly1305.X86.openTo_spSafe v) }
    (openToOut _) (hs := openTo_scrub v)

/-- `vg_chacha20_poly1305_seal_gather`, calling `seal`'s code as
`vg_chacha20_poly1305_seal_core`, as emitted. -/
theorem sealGather_scrubbed (v : XorImpl) :
    VerifiedScrubbed target (Impl.ChaCha20Poly1305.X86.Fn.sealGather v.callee v.suffix)
      (Spec.ChaCha20Poly1305.sealGatherContract X86.abi 824) 0 :=
  verifiedScrubbedF (api := Spec.ChaCha20Poly1305.sealGatherApi)
    { suffix := v.suffix
      code := Impl.ChaCha20Poly1305.X86.SealGather.sealGather (Gather.sealFn v).name (Gather.sealFn v).code
      stack := 824
      verified := Gather.sealGather_verified (Gather.sealFn v)
      spSafe := Gather.sealGather_spSafe v }
    (gatherOut _) (hs := gather_scrub v)

/-! ## Their stack pointer -/

private theorem scrubF_spSafe {rb n : Nat} {c : Prog isa} (h : c.all (fun i => !isa.writesSp i) = true) :
    (Impl.Scrub.X86.scrubF rb n c).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.Scrub.X86.scrubF, Impl.Scrub.X86.wipeBelow, Code.all, h, zeroRegs_all, tail_all,
    Bool.true_and, Bool.and_true]
  exact wipe_all _

theorem seal_spSafe (v : XorImpl) :
    (Impl.ChaCha20Poly1305.X86.Fn.«seal» v.callee).all (fun i => !X86.isa.writesSp i) = true :=
  scrubF_spSafe (Proof.ChaCha20Poly1305.X86.withStackScratchWiped_spSafe
    (Proof.ChaCha20Poly1305.X86.seal_spSafe v))

theorem open_spSafe (v : XorImpl) :
    (Impl.ChaCha20Poly1305.X86.Fn.«open» v.callee).all (fun i => !X86.isa.writesSp i) = true :=
  scrubF_spSafe (Proof.ChaCha20Poly1305.X86.withStackScratchWiped_spSafe
    (Proof.ChaCha20Poly1305.X86.open_spSafe v))

theorem openTo_spSafe (v : XorImpl) :
    (Impl.ChaCha20Poly1305.X86.Fn.openTo v.callee).all (fun i => !X86.isa.writesSp i) = true :=
  scrubF_spSafe (Proof.ChaCha20Poly1305.X86.withStackScratchWiped_spSafe
    (Proof.ChaCha20Poly1305.X86.openTo_spSafe v))

theorem sealGather_spSafe (v : XorImpl) :
    (Impl.ChaCha20Poly1305.X86.Fn.sealGather v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true :=
  scrubF_spSafe (Gather.sealGather_spSafe v)

end VG.Proof.ChaCha20Poly1305.X86.Scrub
