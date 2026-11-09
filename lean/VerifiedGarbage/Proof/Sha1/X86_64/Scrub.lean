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
# SHA-1 on x86-64: `init` without secret residue

Each `init`, followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`), which clears the registers the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Its postcondition reads the memory
on return only within the streaming state (`Stream.repr_congr`).
-/

@[expose] public section

namespace VG.Proof.Sha1.X86_64

open VG.Spec.Sha1 VG.X86_64 VG.X86_64.Scrub

theorem agreeBuf {m₁ m₂ : Mem} {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := fun i hi =>
  (h _ (Offset.contains_base _ (by omega) (by omega))).symm

theorem initOut : PostOut (initContract X86_64.abi) (initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 0) hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hb
    exact Stream.repr_congr (fun i hi => agreeBuf (n := 84 * Elem.size .u8) (by decide) hb i
      (by simp only [Elem.size]; omega)) h

def initKs : List Nat := keep_for% Spec.Sha1.initApi.sig 0 (Impl.Sha1.X86_64.Stream.init) []

theorem initOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha1.initApi.sig 0 []) (Impl.Sha1.X86_64.Stream.init)
      h).any (RScrub.resOkB · 0 initKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of initKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `initApi`'s function, without secret residue. -/
def initReg : Registration Spec.Sha1.initApi X86_64.target :=
  withScrub { code := Impl.Sha1.X86_64.Stream.init, verified := Shared.init } initOut [] (pubOk_nil _)
    (some ⟨initKs, initOk⟩)

end VG.Proof.Sha1.X86_64
