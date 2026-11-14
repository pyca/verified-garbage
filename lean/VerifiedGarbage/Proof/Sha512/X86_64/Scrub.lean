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
# The SHA-512 family's `init` on x86-64, without secret residue

`vg_sha384_init`, `vg_sha512_init`, `vg_sha512_224_init` and
`vg_sha512_256_init`, each followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`), which clears the registers it writes. Their
postconditions read the memory on return only within the streaming state
(`Stream.repr_congr`). HMAC, PBKDF2 and Ed25519 call their code as the
internal `vg_<alg>_init_core` (`Proof.Pbkdf2.Md.X86_64.Sha512.hash`), which
clears what it leaves itself.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64

open VG.X86_64 VG.X86_64.Scrub

theorem initOut (iv : Spec.Sha512.HashValue) :
    PostOut (Spec.Sha512.initContract X86_64.abi iv) (Spec.Sha512.initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 0) hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Sha512.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq] at hb
    exact Stream.repr_congr (fun i hi => (hb _ (Offset.contains_base _
      (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hi]))).symm) h

def init384Ks : List Nat := keep_for% Spec.Sha512.init384Api.sig 0 (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_384) []

theorem init384Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha512.init384Api.sig 0 []) (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_384)
      h).any (RScrub.resOkB · 0 init384Ks (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of init384Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sha384_init`. -/
def init384Reg : Registration Spec.Sha512.init384Api X86_64.target :=
  withScrub { code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_384, verified := Shared.init Spec.Sha512.H0_384 } (initOut Spec.Sha512.H0_384) []
    (pubOk_nil _) (some ⟨init384Ks, init384Ok⟩)

def init512Ks : List Nat := keep_for% Spec.Sha512.init512Api.sig 0 (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512) []

theorem init512Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha512.init512Api.sig 0 []) (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512)
      h).any (RScrub.resOkB · 0 init512Ks (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of init512Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sha512_init`. -/
def init512Reg : Registration Spec.Sha512.init512Api X86_64.target :=
  withScrub { code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512, verified := Shared.init Spec.Sha512.H0_512 } (initOut Spec.Sha512.H0_512) []
    (pubOk_nil _) (some ⟨init512Ks, init512Ok⟩)

def init512_224Ks : List Nat := keep_for% Spec.Sha512.init512_224Api.sig 0 (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_224) []

theorem init512_224Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha512.init512_224Api.sig 0 []) (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_224)
      h).any (RScrub.resOkB · 0 init512_224Ks (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of init512_224Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sha512_224_init`. -/
def init512_224Reg : Registration Spec.Sha512.init512_224Api X86_64.target :=
  withScrub { code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_224, verified := Shared.init Spec.Sha512.H0_512_224 } (initOut Spec.Sha512.H0_512_224) []
    (pubOk_nil _) (some ⟨init512_224Ks, init512_224Ok⟩)

def init512_256Ks : List Nat := keep_for% Spec.Sha512.init512_256Api.sig 0 (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_256) []

theorem init512_256Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha512.init512_256Api.sig 0 []) (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_256)
      h).any (RScrub.resOkB · 0 init512_256Ks (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of init512_256Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sha512_256_init`. -/
def init512_256Reg : Registration Spec.Sha512.init512_256Api X86_64.target :=
  withScrub { code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_256, verified := Shared.init Spec.Sha512.H0_512_256 } (initOut Spec.Sha512.H0_512_256) []
    (pubOk_nil _) (some ⟨init512_256Ks, init512_256Ok⟩)

end VG.Proof.Sha512.X86_64
