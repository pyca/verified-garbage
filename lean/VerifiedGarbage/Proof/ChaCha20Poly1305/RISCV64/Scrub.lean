module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Gather.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch

meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Verified
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Gather.Verified
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
/-!
# ChaCha20-Poly1305 on RISC-V, without secret residue

`vg_chacha20_poly1305_seal`, `vg_chacha20_poly1305_open`,
`vg_chacha20_poly1305_open_to` and `vg_chacha20_poly1305_seal_gather`, each
followed by `Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.withScrub`),
which clears the caller-saved registers and the stack its frames used.
Their postconditions read the memory on return only within the data and the
tag (`RISCV64.Scrub.PostOut`), as on x86-64
(`Proof/ChaCha20Poly1305/X86_64/Scrub.lean`). They call ChaCha20's and
Poly1305's code, and `vg_chacha20_poly1305_seal_gather` that of
`vg_chacha20_poly1305_seal`, as internal functions of their own
(`vg_poly1305_init_core`, …), since the exported ones now clear their stack.

`seal`, `open`, `open_to` and `seal_gather` instead clear only the runs of
doublewords that the residue analysis (`RISCV64.rtaint`) finds may differ
between two runs (`RISCV64.Scrub.withScrubSel`, `scrubSel_noResidue`). Their
code wipes its working space, which leaves none, or two (`open_to`'s and
`seal_gather`'s).

`postOut_of_local_pre` is `postOut_of_local` for a postcondition that reads
the memory on return only within the buffers when the precondition holds, as
on Arm (`Proof/ChaCha20Poly1305/Arm/Scrub.lean`).
-/

@[expose] public section

namespace VG.RISCV64.Scrub

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers when the precondition holds. -/
theorem postOut_of_local_pre {sig : Sig}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply (sig.words abi.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract abi pre post wa stack leak) (sig.retBits abi.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -, -, -, hpre⟩ := hs
    rw [ScrubAbi.plain.ret, ScrubAbi.plain.mem, ScrubAbi.plain.mem] at hp ⊢
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [ScrubAbi.plain.argsLen _ _ hargs s, List.length_map])
      (by rw [← ScrubAbi.plain.mem s]; exact hpre.1) (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply ScrubAbi.plain.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← ScrubAbi.plain.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

end VG.RISCV64.Scrub

namespace VG.Proof.ChaCha20Poly1305.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.ChaCha20Poly1305

/-! ## Postconditions -/

/-- `seal_gather`'s postcondition reads the memory on return only within
`dst` and `tag`. -/
theorem sealGatherPost_out (pb : Nat) : ∀ vs m m₁ m₂ r,
    vs.length = (Spec.ChaCha20Poly1305.sealGatherSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.ChaCha20Poly1305.sealGatherSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.ChaCha20Poly1305.sealGatherSig.words pb) (Spec.ChaCha20Poly1305.sealGatherPost pb) vs m m₁ r →
      Curry.apply (Spec.ChaCha20Poly1305.sealGatherSig.words pb) (Spec.ChaCha20Poly1305.sealGatherPost pb)
        vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 5
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.ChaCha20Poly1305.sealGatherSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (Spec.ChaCha20Poly1305.sealGatherPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (Spec.ChaCha20Poly1305.sealGatherPost pb) _ m m₂ r
  dsimp only [Curry.apply, Spec.ChaCha20Poly1305.sealGatherPost, ArgWord.ofRaw] at h ⊢
  intro h₁ h₂
  rw [bytesAt_congr_len (p := dst) (agree_of hb.2.2.2.1), bytesAt_congr (p := tag) (agree_of hb.2.2.2.2)]
  exact h h₁ h₂

theorem sealOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.sealContract abi stack) (Spec.ChaCha20Poly1305.sealSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (sealPost_out _)

theorem openOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openZeroContract abi stack) (Spec.ChaCha20Poly1305.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (openZeroPost_out _)

theorem openToOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openToContract abi stack) (Spec.ChaCha20Poly1305.openToSig.retBits 64) :=
  postOut_of_local_pre (openToPost_out _)

theorem gatherOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.sealGatherContract abi stack)
      (Spec.ChaCha20Poly1305.sealGatherSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (sealGatherPost_out _)

/-! ## The registrations -/

/-- `Spec.ChaCha20Poly1305.sealApi`. -/
def sealReg : Registration Spec.ChaCha20Poly1305.sealApi RISCV64.target :=
  withScrubSel {
      code := Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78 (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«seal»)
      verified := Proof.ChaCha20Poly1305.RISCV64.seal_framed } []
    (sealOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (sealOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78 (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«seal»)) 624 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.ChaCha20Poly1305.openZeroApi`. -/
def openReg : Registration Spec.ChaCha20Poly1305.openZeroApi RISCV64.target :=
  withScrubSel {
      code := Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78 (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open»)
      verified := Proof.ChaCha20Poly1305.RISCV64.open_framed } []
    (openOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (openOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78 (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open»)) 624 32
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.ChaCha20Poly1305.openToApi`. -/
def openToReg : Registration Spec.ChaCha20Poly1305.openToApi RISCV64.target :=
  withScrubSel {
      code := Impl.StackScratch.RISCV64.withStackScratchArgsWiped 640 1 78 Impl.ChaCha20Poly1305.RISCV64.openTo
      verified := Proof.ChaCha20Poly1305.RISCV64.openTo_framed } [(640, [(0, 2)])]
    (openToOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (openToOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchArgsWiped 640 1 78 Impl.ChaCha20Poly1305.RISCV64.openTo) 640 32
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.ChaCha20Poly1305.sealGatherApi`. -/
def sealGatherReg : Registration Spec.ChaCha20Poly1305.sealGatherApi RISCV64.target :=
  withScrubSel {
      code := Impl.ChaCha20Poly1305.RISCV64.SealGather.sealGather
      verified := Proof.ChaCha20Poly1305.RISCV64.Gather.sealGather_verified } [(640, [(78, 2)])]
    (gatherOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (gatherOut _) (hbp_nil _)
      (Impl.ChaCha20Poly1305.RISCV64.SealGather.sealGather) 640 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

end VG.Proof.ChaCha20Poly1305.RISCV64.Scrub
