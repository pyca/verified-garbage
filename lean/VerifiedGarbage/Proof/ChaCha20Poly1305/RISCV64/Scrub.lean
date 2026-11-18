module

public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubPre
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Gather.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch

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
-/

@[expose] public section

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
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78 (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«seal»)
      verified := Proof.ChaCha20Poly1305.RISCV64.seal_framed }
    (sealOut _)

/-- `Spec.ChaCha20Poly1305.openZeroApi`. -/
def openReg : Registration Spec.ChaCha20Poly1305.openZeroApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78 (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open»)
      verified := Proof.ChaCha20Poly1305.RISCV64.open_framed }
    (openOut _)

/-- `Spec.ChaCha20Poly1305.openToApi`. -/
def openToReg : Registration Spec.ChaCha20Poly1305.openToApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratchArgsWiped 640 1 78 Impl.ChaCha20Poly1305.RISCV64.openTo
      verified := Proof.ChaCha20Poly1305.RISCV64.openTo_framed }
    (openToOut _)

/-- `Spec.ChaCha20Poly1305.sealGatherApi`. -/
def sealGatherReg : Registration Spec.ChaCha20Poly1305.sealGatherApi RISCV64.target :=
  withScrub {
      code := Impl.ChaCha20Poly1305.RISCV64.SealGather.sealGather
      verified := Proof.ChaCha20Poly1305.RISCV64.Gather.sealGather_verified }
    (gatherOut _)

end VG.Proof.ChaCha20Poly1305.RISCV64.Scrub
