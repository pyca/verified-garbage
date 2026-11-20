module

public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Proof.Framework.Arm.Scrub

-- separate module: what every curve's verification on 32-bit ARM needs to be scrubbed, not one curve's proof

/-!
# ECDSA verification on 32-bit ARM, without secret residue

The postcondition of `vg_ecdsa_<curve>_verify` does not read the memory on
return (`Arm.Scrub.PostOut`), as on RISC-V (`Proof/EcKey/RISCV64/Scrub.lean`):
each implementation, whose frame keeps the hash's working values, is
registered followed by a wipe of the stack its contract reserves and
instructions that set the registers a callee may change, but the result, and
the flags to constants (`Impl.Residue.Arm.scrubF`,
`Arm.Scrub.verifiedScrubbedF`). The lemma takes the tables of constants `cs`
the code reads, which may be none.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.Arm.Scrub

open VG.Arm VG.Arm.Scrub

theorem verifyHashOut (J : Spec.Ecdsa.Instance) (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (J.verifyHashContract (abi.withConsts cs) stack) (J.verifyHashSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen _ h => by
    obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    exact h

end VG.Proof.Ecdsa.Verify.Arm.Scrub
