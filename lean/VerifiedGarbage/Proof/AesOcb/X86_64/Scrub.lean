module

public import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant
public import VerifiedGarbage.Proof.AesOcb.X86_64.Frame
import VerifiedGarbage.Proof.Aes.X86_64.Scrub
import VerifiedGarbage.Proof.Aes.X86_64.ModesScrub

/-!
# AES-OCB's key setup on x86-64, without secret residue

`vg_aes_ocb_init` over an implementation of the AES block functions
(`Aes.X86_64.BlocksImpl`) whose encryption and key expansion need no working
space (`BlocksImpl.free`), in a frame of only the 24 bytes it writes itself
(`initF_framed`), followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`) where the implementation gives its residue
analysis (`BlocksImpl.ocbInitRes`). Over the others, as before, in a frame of
2.5 KB, of which the analysis cannot tell what may hold secrets. Its
postcondition reads the memory on return only within the key context, for a
key of the lengths the precondition allows (`X86_64.Scrub.PostOut`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Proof.Aes.X86_64

theorem ocbInitOut (stack : Nat) :
    PostOut (Spec.Ocb.initContract X86_64.abi stack) (Spec.Ocb.initSig.retBits 64) :=
  Proof.Aes.X86_64.Scrub.postOut_of_local_pre fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [k, ln, ctx], _ =>
      simp only [Spec.Ocb.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      change Spec.Ocb.KeyRepr m₁ ctx _ at h
      change Spec.Ocb.KeyRepr m₂ ctx _
      change _ ∨ _ at hpre
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ?_⟩
      · rw [ModesScrub.bytesAt_of0 hb.2 ?_]
        · exact h1
        · simp only [Spec.Aes.bytesAt, List.length_map, List.length_range, Spec.Aes.rounds, Elem.size]
          rcases hpre with h | h | h <;> rw [h] <;> decide
      · simp only [Spec.Ocb.ctxLstar, Spec.Ocb.blockAtMem] at h2 ⊢
        rw [show (240 : BitVec 64) = BitVec.ofNat 64 240 from rfl] at h2 ⊢
        rw [ModesScrub.bytesAt_of hb.2 (by decide)]
        exact h2

open VG.X86_64.RScrub in
/-- `vg_aes_ocb_init` over `v`: with no working space for an implementation
whose encryption and key expansion need none (`BlocksImpl.free`), and then
without secret residue where the analysis handles it. -/
def ocbInitReg (v : BlocksImpl) : Registration Spec.Ocb.initApi X86_64.target :=
  match v.free with
  | some f =>
    withScrub {
      suffix := v.suffix
      code := Proof.Aes.X86_64.ocbInitCodeF v.enc v.dec v.expand
      stack := 40
      verified := Proof.AesOcb.X86_64.initF_framed v f
      spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.AesOcb.X86_64.init_spSafe v) }
      (ocbInitOut _) [] (pubOk_nil _) v.ocbInitRes
  | none => {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesOcb.X86_64.init ⟨v.enc, v.dec, v.expand⟩)
      stack := 2576
      verified := Proof.AesOcb.X86_64.init_framed v
      spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.AesOcb.X86_64.init_spSafe v) }

end VG.Proof.AesOcb.X86_64.Scrub
