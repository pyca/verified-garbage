module

public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Ed25519.WholeLocal

/-!
# Ed25519 on x86-64, without secret residue

The postconditions of `vg_ed25519_key_pair` and `vg_ed25519_sign_expanded`
read the memory on return only within their outputs, and that of
`vg_ed25519_verify` not at all (`X86_64.Scrub.PostOut`), whatever tables of
constants their code takes: each implementation returns with its whole stack
wiped (`X86_64.Scrub.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub
open VG.Proof.Ed25519.WholeLocal (bytesAt_congr)

variable (cs : List (String × List (BitVec 64))) (stack : Nat)

theorem keyPairOut :
    PostOut (Spec.Ed25519.keyPairContract (X86_64.abi.withConsts cs) stack) (Spec.Ed25519.keyPairSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, ex, sd, sc], _ =>
      simp only [Spec.Ed25519.keyPairSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Ed25519.bytesAt m₂ ex 64 = _ ∧ Spec.Ed25519.bytesAt m₂ o 32 = _
      rw [bytesAt_congr hb.2.1, bytesAt_congr hb.1]
      exact h

theorem signExpandedOut :
    PostOut (Spec.Ed25519.signExpandedContract (X86_64.abi.withConsts cs) stack)
      (Spec.Ed25519.signExpandedSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, ex, pk, msg, len, sc], _ =>
      simp only [Spec.Ed25519.signExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      show ∀ seed : List Byte, _ → _ → Spec.Ed25519.bytesAt m₂ o 64 = _
      rw [bytesAt_congr hb.1]
      exact h

theorem verifyOut :
    PostOut (Spec.Ed25519.verifyContract (X86_64.abi.withConsts cs) stack) (Spec.Ed25519.verifySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _], _ => exact h

end VG.Proof.Ed25519.X86_64.Scrub
