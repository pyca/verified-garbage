module

public import VerifiedGarbage.Proof.Ct.X86
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.Ct.X86
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Constant-time comparison on x86 (32-bit), without secret residue

`vg_ct_eq` as emitted (`Impl.Ct.X86.Fn.eq`), followed by the zeroing of the 4 bytes below `esp` its frame
(the caller's `ebx`) used and by `Impl.Scrub.X86.tail`
(`X86.Scrub.verifiedScrubbedAll`), which clears `eax`, `ecx` and `edx` but the result's
bits, the flags and `xmm0`–`xmm7`. Its postcondition reads no memory on
return: it writes none (`X86.Scrub.PostOut`), as on the other targets
(`Proof/Ct/PPC64LE/Scrub.lean`). The cleanup's side condition (`scrubFSide`)
is proved by the kernel's evaluation of it when this module is built.
-/

@[expose] public section

namespace VG.Proof.Ct.X86.Scrub

open VG.X86 VG.X86.Scrub

/-! ## Postconditions -/

theorem eqOut (stack : Nat) : PostOut (Spec.Ct.eqContract abi stack) (Spec.Ct.eqSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    obtain ⟨a, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨b, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨bl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    exact h

/-! ## The function as emitted -/

/-- `Spec.Ct.eqApi` as emitted (`Impl.Ct.X86.Fn.eq`) meets its contract
in constant time and returns without secret residue. -/
theorem eq_scrubbed :
    VerifiedScrubbed X86.target Impl.Ct.X86.Fn.eq (Spec.Ct.eqContract X86.abi 4) 32 :=
  verifiedScrubbedAll (api := Spec.Ct.eqApi)
    { code := Impl.Ct.X86.eq
      verified := Proof.Ct.X86.verified }
    (eqOut _)

end VG.Proof.Ct.X86.Scrub
