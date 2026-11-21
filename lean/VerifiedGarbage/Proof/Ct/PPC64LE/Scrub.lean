module

public import VerifiedGarbage.Impl.Ct.PPC64LE.Fn
public import VerifiedGarbage.Proof.Ct.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Constant-time comparison on PPC64LE, without secret residue

`vg_ct_eq`, followed by `Impl.Scrub.PPC64LE.scrubTail`
(`PPC64LE.Scrub.verifiedScrubbedAll`), which clears the volatile registers it writes.
It has no frames, so there is no stack to wipe. Its postcondition reads no
memory on return: it writes none (`PPC64LE.Scrub.PostOut`), as RISC-V's
(`Proof/Ct/RISCV64Scrub.lean`). `verifiedScrubbedAll`'s side condition (`scrubSide`) is
proved at the theorem, by the kernel's evaluation of it when this
module is built.
-/

@[expose] public section

namespace VG.Proof.Ct.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

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

/-! ## The registration -/

/-- `vg_ct_eq` as emitted (`Impl.Ct.PPC64LE.Fn.eq`) meets its contract in constant
time and returns without secret residue. -/
theorem eq_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Ct.PPC64LE.Fn.eq
      (Spec.Ct.eqContract PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ct.eqApi) {
      code := Impl.Ct.PPC64LE.eq
      verified := Proof.Ct.PPC64LE.verified }
    0 ⟨false, true, [.r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    eqOut
    (by dsimp only; lit_decide)

end VG.Proof.Ct.PPC64LE.Scrub
