module

import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Proof.Ct.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Ct.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration

/-!
# Constant-time comparison on x86-64, without secret residue

`vg_ct_eq`, followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`), which clears the registers that the residue
analysis (`X86_64.RTaint`) finds may hold secrets. Its postcondition reads
only the memory on entry (`X86_64.Scrub.PostOut`).
-/

@[expose] public section

namespace VG.Proof.Ct.X86_64

open VG.X86_64 VG.X86_64.Scrub

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

def eqKs : List Nat := keep_for% Spec.Ct.eqApi.sig 0 Impl.Ct.X86_64.eq []

theorem eqOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Ct.eqApi.sig 0 []) Impl.Ct.X86_64.eq
      h).any (RScrub.resOkB · 0 eqKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of eqKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_ct_eq`. -/
def eqReg : Registration Spec.Ct.eqApi X86_64.target :=
  scrubOf { code := Impl.Ct.X86_64.eq, verified := verified } .sse false [.r8, .r9, .r10] eqOut [] (pubOk_nil _)
    ⟨eqKs, eqOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

end VG.Proof.Ct.X86_64
