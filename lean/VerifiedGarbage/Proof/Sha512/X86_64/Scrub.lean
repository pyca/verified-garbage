module

public import VerifiedGarbage.Spec.Sha512.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha512.X86_64.Shared
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Spec.Sha512.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sha512.X86_64.Shared
meta import VerifiedGarbage.Proof.Sha512.Stream
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 on x86-64: `init` without secret residue

Each `init`, followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`), which clears the registers the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Its postcondition reads the memory
on return only within the streaming state (`Stream.repr_congr`).
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64

open VG.Spec.Sha512 VG.X86_64 VG.X86_64.Scrub

theorem agreeBuf {m₁ m₂ : Mem} {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := fun i hi =>
  (h _ (Offset.contains_base _ (by omega) (by omega))).symm

theorem initOut (iv : HashValue) : PostOut (initContract X86_64.abi iv) (initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 0) hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hb
    exact Stream.repr_congr (fun i hi => agreeBuf (n := 192 * Elem.size .u8) (by decide) hb i
      (by simp only [Elem.size]; omega)) h

/-! One registration per initial hash value. -/

def init384Ks : List Nat := keep_for% Spec.Sha512.init384Api.sig 0 (Impl.Sha512.X86_64.Stream.init H0_384) []

theorem init384Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha512.init384Api.sig 0 []) (Impl.Sha512.X86_64.Stream.init H0_384)
      h).any (RScrub.resOkB · 0 init384Ks (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of init384Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `init384Api`'s function, without secret residue. -/
def init384Reg : Registration Spec.Sha512.init384Api X86_64.target :=
  withScrub { code := Impl.Sha512.X86_64.Stream.init H0_384, verified := Shared.init H0_384 }
    (initOut H0_384) [] (pubOk_nil _)
    (some ⟨init384Ks, init384Ok⟩)

def init512Ks : List Nat := keep_for% Spec.Sha512.init512Api.sig 0 (Impl.Sha512.X86_64.Stream.init H0_512) []

theorem init512Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha512.init512Api.sig 0 []) (Impl.Sha512.X86_64.Stream.init H0_512)
      h).any (RScrub.resOkB · 0 init512Ks (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of init512Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `init512Api`'s function, without secret residue. -/
def init512Reg : Registration Spec.Sha512.init512Api X86_64.target :=
  withScrub { code := Impl.Sha512.X86_64.Stream.init H0_512, verified := Shared.init H0_512 }
    (initOut H0_512) [] (pubOk_nil _)
    (some ⟨init512Ks, init512Ok⟩)

def init512_224Ks : List Nat := keep_for% Spec.Sha512.init512_224Api.sig 0 (Impl.Sha512.X86_64.Stream.init H0_512_224) []

theorem init512_224Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha512.init512_224Api.sig 0 []) (Impl.Sha512.X86_64.Stream.init H0_512_224)
      h).any (RScrub.resOkB · 0 init512_224Ks (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of init512_224Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `init512_224Api`'s function, without secret residue. -/
def init512_224Reg : Registration Spec.Sha512.init512_224Api X86_64.target :=
  withScrub { code := Impl.Sha512.X86_64.Stream.init H0_512_224, verified := Shared.init H0_512_224 }
    (initOut H0_512_224) [] (pubOk_nil _)
    (some ⟨init512_224Ks, init512_224Ok⟩)

def init512_256Ks : List Nat := keep_for% Spec.Sha512.init512_256Api.sig 0 (Impl.Sha512.X86_64.Stream.init H0_512_256) []

theorem init512_256Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha512.init512_256Api.sig 0 []) (Impl.Sha512.X86_64.Stream.init H0_512_256)
      h).any (RScrub.resOkB · 0 init512_256Ks (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of init512_256Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `init512_256Api`'s function, without secret residue. -/
def init512_256Reg : Registration Spec.Sha512.init512_256Api X86_64.target :=
  withScrub { code := Impl.Sha512.X86_64.Stream.init H0_512_256, verified := Shared.init H0_512_256 }
    (initOut H0_512_256) [] (pubOk_nil _)
    (some ⟨init512_256Ks, init512_256Ok⟩)

end VG.Proof.Sha512.X86_64
