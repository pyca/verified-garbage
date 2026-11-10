module

public import VerifiedGarbage.Spec.Sha1.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha1.X86_64.Shared
import VerifiedGarbage.Proof.Sha1.Stream
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Spec.Sha1.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sha1.X86_64.Shared
meta import VerifiedGarbage.Proof.Sha1.Stream
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_sha1_init` on x86-64, without secret residue

`vg_sha1_init`, followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`), which clears the registers it writes. Its
postcondition reads the memory on return only within the streaming state
(`Stream.repr_congr`). HMAC-SHA1, PBKDF2-HMAC-SHA1 and DSA call its code as
the internal `vg_sha1_init_core` (`Proof.Pbkdf2.Md.X86_64.Sha1.hash`), which
clears what it leaves itself.
-/

@[expose] public section

namespace VG.Proof.Sha1.X86_64

open VG.Spec.Sha1 VG.X86_64 VG.X86_64.Scrub

theorem initOut : PostOut (initContract X86_64.abi) (initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 0) hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hb
    exact Stream.repr_congr (fun i hi => (hb _ (Offset.contains_base _
      (by simp only [Elem.size]; omega) (by omega))).symm) h

def initKs : List Nat := keep_for% Spec.Sha1.initApi.sig 0 Impl.Sha1.X86_64.Stream.init []

theorem initOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha1.initApi.sig 0 []) Impl.Sha1.X86_64.Stream.init
      h).any (RScrub.resOkB · 0 initKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of initKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sha1_init`. -/
def initReg : Registration Spec.Sha1.initApi X86_64.target :=
  withScrub { code := Impl.Sha1.X86_64.Stream.init, verified := Shared.init } initOut []
    (pubOk_nil _) (some ⟨initKs, initOk⟩)

end VG.Proof.Sha1.X86_64
