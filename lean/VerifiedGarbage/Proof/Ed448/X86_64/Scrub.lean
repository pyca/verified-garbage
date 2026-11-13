module

public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Ed448.WholeLocal

/-!
# Ed448 on x86-64, without secret residue

The postconditions of `vg_ed448_public_key` and `vg_ed448_sign_cached` read
the memory on return only within their outputs, and that of
`vg_ed448_verify` not at all (`X86_64.Scrub.PostOut`): each implementation
returns with its whole stack wiped (`X86_64.Scrub.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub
open VG.Proof.Ed448.WholeLocal (bytesAt_congr)

variable (stack : Nat)

theorem publicKeyOut :
    PostOut (Spec.Ed448.publicKeyContract X86_64.abi stack) (Spec.Ed448.publicKeySig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, sd, sc], _ =>
      simp only [Spec.Ed448.publicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Ed448.bytesAt m₂ o 57 = _
      rw [bytesAt_congr hb.1]
      exact h

theorem signCachedOut :
    PostOut (Spec.Ed448.signCachedContract X86_64.abi stack) (Spec.Ed448.signCachedSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, sd, pk, ctx, cl, msg, len, sc], _ =>
      simp only [Spec.Ed448.signCachedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Ed448.bytesAt m₂ o 114 = _
      rw [bytesAt_congr hb.1]
      exact h

theorem verifyOut :
    PostOut (Spec.Ed448.verifyContract X86_64.abi stack) (Spec.Ed448.verifySig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _], _ => exact h

end VG.Proof.Ed448.X86_64.Scrub
