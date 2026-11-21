module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubSel
public import VerifiedGarbage.Impl.Ct.X86_64.Fn
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

/-! ## The functions as emitted -/

theorem eq_codeSp : (Impl.Ct.X86_64.eq).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Ct.eqApi`'s function as emitted (`Impl.Ct.X86_64.Fn.eq`) meets its contract in
constant time and returns without secret residue. -/
theorem eq_scrubbed :
    VerifiedScrubbed target Impl.Ct.X86_64.Fn.eq (Spec.Ct.eqApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedSel (api := Spec.Ct.eqApi)
    { code := Impl.Ct.X86_64.eq
      verified := verified
      spSafe := eq_codeSp }
    .sse [] eqOut (RScrub.pubOk_nil _) (by taint_decide)

theorem eq_spSafe : Impl.Ct.X86_64.Fn.eq.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe eq_codeSp
end VG.Proof.Ct.X86_64
