module

public import VerifiedGarbage.Spec.Sha3.Instances
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.Sha3.Instances

/-!
# SHA-3 on AArch64, without secret residue

The postconditions of `vg_<f>_update`, `vg_<f>_finalize` and
`vg_<f>_squeeze` read the memory on return only within the state and the
output (`ScrubAll.ScrubAllOk`): each implementation, generic over the
Keccak-f[1600] implementation it calls, returns with every register it may
leave secret cleared and its whole stack zeroed (`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.Sha3
open VG.Proof.Sha3.Instances (stateAt_agree finalizePostOut_local xofFinalizePostOut_local
  xofSqueezePostOut_local)

/-- `updatePost` reads the memory on return only within the state. -/
theorem updatePostOut_local (rate pb : Nat) : ∀ vs m m₁ m₂ r,
    vs.length = (updateSig.words pb).length →
    (∀ b ∈ Sig.bufs updateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSig.words pb) (updatePost rate pb) vs m m₁ r →
      Curry.apply (updateSig.words pb) (updatePost rate pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [_, _, _, _, _], _ =>
    simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (updatePost rate pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (updatePost rate pb) _ m m₂ r
    dsimp only [Curry.apply, updatePost, ArgWord.ofRaw, Spec.Sha3.Repr] at h ⊢
    refine ⟨fun msg hr hc => ?_, h.2⟩
    rw [stateAt_agree hb.1]
    exact h.1 msg hr hc

theorem updateOk (rate : Nat) :
    ScrubAllOk (updateContract abi rate 16) 16 (updateSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := updateSig) (by decide) (W := 16) (by decide) (Nat.le_refl _)
    (updatePostOut_local rate _)

theorem finalizeOk (H : HashFn) :
    ScrubAllOk (finalizeContract abi H (16 + 672)) (16 + 672) ((finalizeSig H.len).retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := finalizeSig H.len) (Nat.le_of_ble_eq_true rfl) (W := 16 + 672) (by decide)
    (Nat.le_refl _) (finalizePostOut_local _ H)

theorem xofFinalizeOk (X : Xof) :
    ScrubAllOk (xofFinalizeContract abi X (16 + 640)) (16 + 640) (xofFinalizeSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := xofFinalizeSig) (by decide) (W := 16 + 640) (by decide) (Nat.le_refl _)
    (xofFinalizePostOut_local _ X)

theorem xofSqueezeOk (X : Xof) :
    ScrubAllOk (xofSqueezeContract abi X (16 + 640)) (16 + 640) (xofSqueezeSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := xofSqueezeSig) (by decide) (W := 16 + 640) (by decide) (Nat.le_refl _)
    (xofSqueezePostOut_local _ X)

end VG.Proof.Sha3.AArch64.Scrub
