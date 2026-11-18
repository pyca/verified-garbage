module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ct.RISCV64

/-!
# Constant-time comparison on RISC-V, without secret residue

`vg_ct_eq`, each followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within nothing: it writes no memory (`RISCV64.Scrub.PostOut`), as on x86-64 (`Proof/Ct/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Ct.RISCV64Scrub

open VG.RISCV64 VG.RISCV64.Scrub

/-! ## Postconditions -/

theorem eqOut : PostOut (Spec.Ct.eqContract abi) (Spec.Ct.eqSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    obtain ⟨a, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨b, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨bl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    exact h

/-! ## The registrations -/

/-- `Spec.Ct.eqApi`. -/
def eqReg : Registration Spec.Ct.eqApi RISCV64.target :=
  withScrub {
      code := Impl.Ct.RISCV64.eq
      verified := Proof.Ct.RISCV64.verified }
    (eqOut)

end VG.Proof.Ct.RISCV64Scrub
